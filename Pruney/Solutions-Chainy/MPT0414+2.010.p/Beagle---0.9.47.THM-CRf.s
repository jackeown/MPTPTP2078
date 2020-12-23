%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 16.72s
% Output     : CNFRefutation 16.85s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 183 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 460 expanded)
%              Number of equality atoms :   16 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_28,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | k1_xboole_0 = B_11
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_172,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_182,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_58,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_172])).

tff(c_34,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_6')
      | ~ r2_hidden(D_27,'#skF_7')
      | ~ m1_subset_1(D_27,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_198,plain,(
    ! [A_59] :
      ( r2_hidden(A_59,'#skF_6')
      | ~ r2_hidden(A_59,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_182,c_34])).

tff(c_472,plain,(
    ! [B_74] :
      ( r2_hidden('#skF_2'('#skF_7',B_74),'#skF_6')
      | r1_tarski('#skF_7',B_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_493,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_472,c_8])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1('#skF_4'(A_13,B_14),A_13)
      | B_14 = A_13
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_7')
      | ~ r2_hidden(D_35,'#skF_6')
      | ~ m1_subset_1(D_35,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_96,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,'#skF_7')
      | ~ r2_hidden(A_48,'#skF_6')
      | ~ r1_tarski(A_48,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_48,'#skF_6')
      | ~ r1_tarski(A_48,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_109,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,
    ( r2_hidden('#skF_1'('#skF_7'),'#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_198])).

tff(c_226,plain,(
    r2_hidden('#skF_1'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_217])).

tff(c_233,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_226,c_2])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_234,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_60,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_172])).

tff(c_36,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_7')
      | ~ r2_hidden(D_27,'#skF_6')
      | ~ m1_subset_1(D_27,k1_zfmisc_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_244,plain,(
    ! [A_60] :
      ( r2_hidden(A_60,'#skF_7')
      | ~ r2_hidden(A_60,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_234,c_36])).

tff(c_377,plain,(
    ! [A_69,B_70] :
      ( ~ r2_hidden('#skF_4'(A_69,B_70),B_70)
      | B_70 = A_69
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2137,plain,(
    ! [A_155] :
      ( A_155 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_155))
      | ~ r2_hidden('#skF_4'(A_155,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_244,c_377])).

tff(c_2146,plain,(
    ! [A_155] :
      ( A_155 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_155))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1('#skF_4'(A_155,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_2137])).

tff(c_17536,plain,(
    ! [A_627] :
      ( A_627 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_627))
      | ~ m1_subset_1('#skF_4'(A_627,'#skF_7'),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_2146])).

tff(c_17540,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_18,c_17536])).

tff(c_17543,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_17540])).

tff(c_17663,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_17543])).

tff(c_17667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_17663])).

tff(c_17669,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_17709,plain,(
    ! [A_634,C_635,B_636] :
      ( m1_subset_1(A_634,C_635)
      | ~ m1_subset_1(B_636,k1_zfmisc_1(C_635))
      | ~ r2_hidden(A_634,B_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17772,plain,(
    ! [A_641] :
      ( m1_subset_1(A_641,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_641,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_17709])).

tff(c_17784,plain,(
    ! [A_642] :
      ( r2_hidden(A_642,'#skF_7')
      | ~ r2_hidden(A_642,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_17772,c_36])).

tff(c_17799,plain,(
    ! [A_642] :
      ( ~ v1_xboole_0('#skF_7')
      | ~ r2_hidden(A_642,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_17784,c_2])).

tff(c_17806,plain,(
    ! [A_642] : ~ r2_hidden(A_642,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17669,c_17799])).

tff(c_17720,plain,(
    ! [A_638] :
      ( m1_subset_1(A_638,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_638,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_17709])).

tff(c_17733,plain,(
    ! [A_638] :
      ( r2_hidden(A_638,'#skF_6')
      | ~ r2_hidden(A_638,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_17720,c_34])).

tff(c_17842,plain,(
    ! [A_646] : ~ r2_hidden(A_646,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_17806,c_17733])).

tff(c_17859,plain,(
    ! [A_10] :
      ( k1_xboole_0 = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_12,c_17842])).

tff(c_17881,plain,(
    ! [A_10] : ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ),
    inference(splitLeft,[status(thm)],[c_17859])).

tff(c_17898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17881,c_30])).

tff(c_17899,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_17859])).

tff(c_17824,plain,(
    ! [A_644,B_645] :
      ( r2_hidden('#skF_3'(A_644,B_645),B_645)
      | k1_xboole_0 = B_645
      | ~ m1_subset_1(B_645,k1_zfmisc_1(A_644)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_17838,plain,(
    ! [A_644] :
      ( k1_xboole_0 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_644)) ) ),
    inference(resolution,[status(thm)],[c_17824,c_17806])).

tff(c_17907,plain,(
    ! [A_644] :
      ( '#skF_7' = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_644)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17899,c_17838])).

tff(c_17908,plain,(
    ! [A_644] : ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_644)) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_17907])).

tff(c_17910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17908,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:20:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.72/7.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.72/7.01  
% 16.72/7.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.72/7.02  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 16.72/7.02  
% 16.72/7.02  %Foreground sorts:
% 16.72/7.02  
% 16.72/7.02  
% 16.72/7.02  %Background operators:
% 16.72/7.02  
% 16.72/7.02  
% 16.72/7.02  %Foreground operators:
% 16.72/7.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.72/7.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.72/7.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.72/7.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.72/7.02  tff('#skF_7', type, '#skF_7': $i).
% 16.72/7.02  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.72/7.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.72/7.02  tff('#skF_5', type, '#skF_5': $i).
% 16.72/7.02  tff('#skF_6', type, '#skF_6': $i).
% 16.72/7.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.72/7.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.72/7.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.72/7.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.72/7.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.72/7.02  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.72/7.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.72/7.02  
% 16.85/7.04  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 16.85/7.04  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 16.85/7.04  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 16.85/7.04  tff(f_75, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 16.85/7.04  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.85/7.04  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_subset_1)).
% 16.85/7.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.85/7.04  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 16.85/7.04  tff(c_28, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_12, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | k1_xboole_0=B_11 | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.85/7.04  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.85/7.04  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_172, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.85/7.04  tff(c_182, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_58, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_172])).
% 16.85/7.04  tff(c_34, plain, (![D_27]: (r2_hidden(D_27, '#skF_6') | ~r2_hidden(D_27, '#skF_7') | ~m1_subset_1(D_27, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_198, plain, (![A_59]: (r2_hidden(A_59, '#skF_6') | ~r2_hidden(A_59, '#skF_7'))), inference(resolution, [status(thm)], [c_182, c_34])).
% 16.85/7.04  tff(c_472, plain, (![B_74]: (r2_hidden('#skF_2'('#skF_7', B_74), '#skF_6') | r1_tarski('#skF_7', B_74))), inference(resolution, [status(thm)], [c_10, c_198])).
% 16.85/7.04  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.85/7.04  tff(c_493, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_472, c_8])).
% 16.85/7.04  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.85/7.04  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1('#skF_4'(A_13, B_14), A_13) | B_14=A_13 | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.85/7.04  tff(c_57, plain, (![D_35]: (r2_hidden(D_35, '#skF_7') | ~r2_hidden(D_35, '#skF_6') | ~m1_subset_1(D_35, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_96, plain, (![A_48]: (r2_hidden(A_48, '#skF_7') | ~r2_hidden(A_48, '#skF_6') | ~r1_tarski(A_48, '#skF_5'))), inference(resolution, [status(thm)], [c_24, c_57])).
% 16.85/7.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.85/7.04  tff(c_108, plain, (![A_48]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_48, '#skF_6') | ~r1_tarski(A_48, '#skF_5'))), inference(resolution, [status(thm)], [c_96, c_2])).
% 16.85/7.04  tff(c_109, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_108])).
% 16.85/7.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.85/7.04  tff(c_217, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_198])).
% 16.85/7.04  tff(c_226, plain, (r2_hidden('#skF_1'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_109, c_217])).
% 16.85/7.04  tff(c_233, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_226, c_2])).
% 16.85/7.04  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, B_17) | v1_xboole_0(B_17) | ~m1_subset_1(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.85/7.04  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_234, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_60, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_172])).
% 16.85/7.04  tff(c_36, plain, (![D_27]: (r2_hidden(D_27, '#skF_7') | ~r2_hidden(D_27, '#skF_6') | ~m1_subset_1(D_27, k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 16.85/7.04  tff(c_244, plain, (![A_60]: (r2_hidden(A_60, '#skF_7') | ~r2_hidden(A_60, '#skF_6'))), inference(resolution, [status(thm)], [c_234, c_36])).
% 16.85/7.04  tff(c_377, plain, (![A_69, B_70]: (~r2_hidden('#skF_4'(A_69, B_70), B_70) | B_70=A_69 | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.85/7.04  tff(c_2137, plain, (![A_155]: (A_155='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_155)) | ~r2_hidden('#skF_4'(A_155, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_244, c_377])).
% 16.85/7.04  tff(c_2146, plain, (![A_155]: (A_155='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_155)) | v1_xboole_0('#skF_6') | ~m1_subset_1('#skF_4'(A_155, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_2137])).
% 16.85/7.04  tff(c_17536, plain, (![A_627]: (A_627='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_627)) | ~m1_subset_1('#skF_4'(A_627, '#skF_7'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_233, c_2146])).
% 16.85/7.04  tff(c_17540, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_17536])).
% 16.85/7.04  tff(c_17543, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_17540])).
% 16.85/7.04  tff(c_17663, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_24, c_17543])).
% 16.85/7.04  tff(c_17667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_493, c_17663])).
% 16.85/7.04  tff(c_17669, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_108])).
% 16.85/7.04  tff(c_17709, plain, (![A_634, C_635, B_636]: (m1_subset_1(A_634, C_635) | ~m1_subset_1(B_636, k1_zfmisc_1(C_635)) | ~r2_hidden(A_634, B_636))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.85/7.04  tff(c_17772, plain, (![A_641]: (m1_subset_1(A_641, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_641, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_17709])).
% 16.85/7.04  tff(c_17784, plain, (![A_642]: (r2_hidden(A_642, '#skF_7') | ~r2_hidden(A_642, '#skF_6'))), inference(resolution, [status(thm)], [c_17772, c_36])).
% 16.85/7.04  tff(c_17799, plain, (![A_642]: (~v1_xboole_0('#skF_7') | ~r2_hidden(A_642, '#skF_6'))), inference(resolution, [status(thm)], [c_17784, c_2])).
% 16.85/7.04  tff(c_17806, plain, (![A_642]: (~r2_hidden(A_642, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_17669, c_17799])).
% 16.85/7.04  tff(c_17720, plain, (![A_638]: (m1_subset_1(A_638, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_638, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_17709])).
% 16.85/7.04  tff(c_17733, plain, (![A_638]: (r2_hidden(A_638, '#skF_6') | ~r2_hidden(A_638, '#skF_7'))), inference(resolution, [status(thm)], [c_17720, c_34])).
% 16.85/7.04  tff(c_17842, plain, (![A_646]: (~r2_hidden(A_646, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_17806, c_17733])).
% 16.85/7.04  tff(c_17859, plain, (![A_10]: (k1_xboole_0='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_12, c_17842])).
% 16.85/7.04  tff(c_17881, plain, (![A_10]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(splitLeft, [status(thm)], [c_17859])).
% 16.85/7.04  tff(c_17898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17881, c_30])).
% 16.85/7.04  tff(c_17899, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_17859])).
% 16.85/7.04  tff(c_17824, plain, (![A_644, B_645]: (r2_hidden('#skF_3'(A_644, B_645), B_645) | k1_xboole_0=B_645 | ~m1_subset_1(B_645, k1_zfmisc_1(A_644)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.85/7.04  tff(c_17838, plain, (![A_644]: (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_644)))), inference(resolution, [status(thm)], [c_17824, c_17806])).
% 16.85/7.04  tff(c_17907, plain, (![A_644]: ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_644)))), inference(demodulation, [status(thm), theory('equality')], [c_17899, c_17838])).
% 16.85/7.04  tff(c_17908, plain, (![A_644]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_644)))), inference(negUnitSimplification, [status(thm)], [c_28, c_17907])).
% 16.85/7.04  tff(c_17910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17908, c_32])).
% 16.85/7.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/7.04  
% 16.85/7.04  Inference rules
% 16.85/7.04  ----------------------
% 16.85/7.04  #Ref     : 0
% 16.85/7.04  #Sup     : 4257
% 16.85/7.04  #Fact    : 0
% 16.85/7.04  #Define  : 0
% 16.85/7.04  #Split   : 38
% 16.85/7.04  #Chain   : 0
% 16.85/7.04  #Close   : 0
% 16.85/7.04  
% 16.85/7.04  Ordering : KBO
% 16.85/7.04  
% 16.85/7.04  Simplification rules
% 16.85/7.04  ----------------------
% 16.85/7.04  #Subsume      : 2205
% 16.85/7.04  #Demod        : 911
% 16.85/7.04  #Tautology    : 342
% 16.85/7.04  #SimpNegUnit  : 261
% 16.85/7.04  #BackRed      : 141
% 16.85/7.04  
% 16.85/7.04  #Partial instantiations: 0
% 16.85/7.04  #Strategies tried      : 1
% 16.85/7.04  
% 16.85/7.04  Timing (in seconds)
% 16.85/7.04  ----------------------
% 16.85/7.05  Preprocessing        : 0.46
% 16.85/7.05  Parsing              : 0.24
% 16.85/7.05  CNF conversion       : 0.04
% 16.85/7.05  Main loop            : 5.66
% 16.85/7.05  Inferencing          : 1.36
% 16.85/7.05  Reduction            : 1.54
% 16.85/7.05  Demodulation         : 0.89
% 16.85/7.05  BG Simplification    : 0.13
% 16.85/7.05  Subsumption          : 2.14
% 16.85/7.05  Abstraction          : 0.16
% 16.85/7.05  MUC search           : 0.00
% 16.85/7.05  Cooper               : 0.00
% 16.85/7.05  Total                : 6.18
% 16.85/7.05  Index Insertion      : 0.00
% 16.85/7.05  Index Deletion       : 0.00
% 16.85/7.05  Index Matching       : 0.00
% 16.85/7.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
