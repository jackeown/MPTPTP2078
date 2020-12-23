%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:23 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 231 expanded)
%              Number of leaves         :   16 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 572 expanded)
%              Number of equality atoms :   20 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [B_20,A_21] :
      ( m1_subset_1(B_20,A_21)
      | ~ v1_xboole_0(B_20)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [C_17] :
      ( ~ r2_hidden(C_17,'#skF_3')
      | ~ m1_subset_1(C_17,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_35,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_32])).

tff(c_50,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_35])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    ! [B_22,A_23] :
      ( m1_subset_1(B_22,A_23)
      | ~ r2_hidden(B_22,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_57,plain,(
    ! [B_24,A_25] :
      ( r2_hidden(B_24,A_25)
      | ~ m1_subset_1(B_24,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [C_12] :
      ( ~ r2_hidden(C_12,'#skF_3')
      | ~ m1_subset_1(C_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_69,plain,(
    ! [B_24] :
      ( ~ m1_subset_1(B_24,'#skF_2')
      | ~ m1_subset_1(B_24,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_57,c_16])).

tff(c_84,plain,(
    ! [B_30] :
      ( ~ m1_subset_1(B_30,'#skF_2')
      | ~ m1_subset_1(B_30,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_88,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_84])).

tff(c_95,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_88])).

tff(c_97,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_101,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_97])).

tff(c_102,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    ! [C_26,A_27,B_28] :
      ( r2_hidden(C_26,A_27)
      | ~ r2_hidden(C_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [B_35,A_36,A_37] :
      ( r2_hidden(B_35,A_36)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_35,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_8,c_71])).

tff(c_144,plain,(
    ! [B_35] :
      ( r2_hidden(B_35,'#skF_2')
      | ~ m1_subset_1(B_35,'#skF_3')
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_136])).

tff(c_150,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_2')
      | ~ m1_subset_1(B_38,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_144])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_38] :
      ( m1_subset_1(B_38,'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(B_38,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_164,plain,(
    ! [B_39] :
      ( m1_subset_1(B_39,'#skF_2')
      | ~ m1_subset_1(B_39,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_155])).

tff(c_83,plain,(
    ! [B_24] :
      ( ~ m1_subset_1(B_24,'#skF_2')
      | ~ m1_subset_1(B_24,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_177,plain,(
    ! [B_40] : ~ m1_subset_1(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_83])).

tff(c_181,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_56,c_177])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_102,c_181])).

tff(c_191,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_22,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_191,c_26])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_194])).

tff(c_199,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_202,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_199,c_26])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_202])).

tff(c_208,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_212,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_208,c_26])).

tff(c_215,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_18])).

tff(c_214,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_290,plain,(
    ! [C_50,A_51,B_52] :
      ( r2_hidden(C_50,A_51)
      | ~ r2_hidden(C_50,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [A_53,A_54] :
      ( r2_hidden('#skF_1'(A_53),A_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_54))
      | A_53 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_214,c_290])).

tff(c_314,plain,(
    ! [A_55,A_56] :
      ( ~ v1_xboole_0(A_55)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(A_55))
      | A_56 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_297,c_4])).

tff(c_325,plain,
    ( ~ v1_xboole_0('#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_314])).

tff(c_330,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_325])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_215,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  
% 2.05/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.25  
% 2.05/1.27  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.05/1.27  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.05/1.27  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.05/1.27  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.05/1.27  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.05/1.27  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_42, plain, (![B_20, A_21]: (m1_subset_1(B_20, A_21) | ~v1_xboole_0(B_20) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.27  tff(c_28, plain, (![C_17]: (~r2_hidden(C_17, '#skF_3') | ~m1_subset_1(C_17, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_32, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2, c_28])).
% 2.05/1.27  tff(c_35, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_32])).
% 2.05/1.27  tff(c_50, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_35])).
% 2.05/1.27  tff(c_51, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 2.05/1.27  tff(c_52, plain, (![B_22, A_23]: (m1_subset_1(B_22, A_23) | ~r2_hidden(B_22, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_56, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.05/1.27  tff(c_57, plain, (![B_24, A_25]: (r2_hidden(B_24, A_25) | ~m1_subset_1(B_24, A_25) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_16, plain, (![C_12]: (~r2_hidden(C_12, '#skF_3') | ~m1_subset_1(C_12, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_69, plain, (![B_24]: (~m1_subset_1(B_24, '#skF_2') | ~m1_subset_1(B_24, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_16])).
% 2.05/1.27  tff(c_84, plain, (![B_30]: (~m1_subset_1(B_30, '#skF_2') | ~m1_subset_1(B_30, '#skF_3'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.05/1.27  tff(c_88, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | v1_xboole_0('#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_84])).
% 2.05/1.27  tff(c_95, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3') | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_51, c_88])).
% 2.05/1.27  tff(c_97, plain, (~m1_subset_1('#skF_1'('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_95])).
% 2.05/1.27  tff(c_101, plain, (~v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_97])).
% 2.05/1.27  tff(c_102, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_101])).
% 2.05/1.27  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.27  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_71, plain, (![C_26, A_27, B_28]: (r2_hidden(C_26, A_27) | ~r2_hidden(C_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.27  tff(c_136, plain, (![B_35, A_36, A_37]: (r2_hidden(B_35, A_36) | ~m1_subset_1(A_37, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_35, A_37) | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_8, c_71])).
% 2.05/1.27  tff(c_144, plain, (![B_35]: (r2_hidden(B_35, '#skF_2') | ~m1_subset_1(B_35, '#skF_3') | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_136])).
% 2.05/1.27  tff(c_150, plain, (![B_38]: (r2_hidden(B_38, '#skF_2') | ~m1_subset_1(B_38, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_102, c_144])).
% 2.05/1.27  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.27  tff(c_155, plain, (![B_38]: (m1_subset_1(B_38, '#skF_2') | v1_xboole_0('#skF_2') | ~m1_subset_1(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_150, c_6])).
% 2.05/1.27  tff(c_164, plain, (![B_39]: (m1_subset_1(B_39, '#skF_2') | ~m1_subset_1(B_39, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_51, c_155])).
% 2.05/1.27  tff(c_83, plain, (![B_24]: (~m1_subset_1(B_24, '#skF_2') | ~m1_subset_1(B_24, '#skF_3'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.05/1.27  tff(c_177, plain, (![B_40]: (~m1_subset_1(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_164, c_83])).
% 2.05/1.27  tff(c_181, plain, (v1_xboole_0('#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_56, c_177])).
% 2.05/1.27  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_102, c_181])).
% 2.05/1.27  tff(c_191, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_101])).
% 2.05/1.27  tff(c_22, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.27  tff(c_4, plain, (![B_4, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.05/1.27  tff(c_26, plain, (![A_15]: (~v1_xboole_0(A_15) | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_22, c_4])).
% 2.05/1.27  tff(c_194, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_191, c_26])).
% 2.05/1.27  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_194])).
% 2.05/1.27  tff(c_199, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_69])).
% 2.05/1.27  tff(c_202, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_199, c_26])).
% 2.05/1.27  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_202])).
% 2.05/1.27  tff(c_208, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 2.05/1.27  tff(c_212, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_208, c_26])).
% 2.05/1.27  tff(c_215, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_18])).
% 2.05/1.27  tff(c_214, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_2])).
% 2.05/1.27  tff(c_290, plain, (![C_50, A_51, B_52]: (r2_hidden(C_50, A_51) | ~r2_hidden(C_50, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.27  tff(c_297, plain, (![A_53, A_54]: (r2_hidden('#skF_1'(A_53), A_54) | ~m1_subset_1(A_53, k1_zfmisc_1(A_54)) | A_53='#skF_2')), inference(resolution, [status(thm)], [c_214, c_290])).
% 2.05/1.27  tff(c_314, plain, (![A_55, A_56]: (~v1_xboole_0(A_55) | ~m1_subset_1(A_56, k1_zfmisc_1(A_55)) | A_56='#skF_2')), inference(resolution, [status(thm)], [c_297, c_4])).
% 2.05/1.27  tff(c_325, plain, (~v1_xboole_0('#skF_2') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_20, c_314])).
% 2.05/1.27  tff(c_330, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_325])).
% 2.05/1.27  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_215, c_330])).
% 2.05/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  Inference rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Ref     : 0
% 2.05/1.27  #Sup     : 59
% 2.05/1.27  #Fact    : 0
% 2.05/1.27  #Define  : 0
% 2.05/1.27  #Split   : 7
% 2.05/1.27  #Chain   : 0
% 2.05/1.27  #Close   : 0
% 2.05/1.27  
% 2.05/1.27  Ordering : KBO
% 2.05/1.27  
% 2.05/1.27  Simplification rules
% 2.05/1.27  ----------------------
% 2.05/1.27  #Subsume      : 15
% 2.05/1.27  #Demod        : 6
% 2.05/1.27  #Tautology    : 10
% 2.05/1.27  #SimpNegUnit  : 11
% 2.05/1.27  #BackRed      : 3
% 2.05/1.27  
% 2.05/1.27  #Partial instantiations: 0
% 2.05/1.27  #Strategies tried      : 1
% 2.05/1.27  
% 2.05/1.27  Timing (in seconds)
% 2.05/1.27  ----------------------
% 2.05/1.27  Preprocessing        : 0.28
% 2.05/1.27  Parsing              : 0.16
% 2.05/1.27  CNF conversion       : 0.02
% 2.05/1.27  Main loop            : 0.21
% 2.05/1.27  Inferencing          : 0.09
% 2.05/1.27  Reduction            : 0.05
% 2.05/1.27  Demodulation         : 0.03
% 2.05/1.27  BG Simplification    : 0.01
% 2.05/1.27  Subsumption          : 0.05
% 2.05/1.27  Abstraction          : 0.01
% 2.05/1.27  MUC search           : 0.00
% 2.05/1.27  Cooper               : 0.00
% 2.05/1.27  Total                : 0.53
% 2.05/1.27  Index Insertion      : 0.00
% 2.05/1.27  Index Deletion       : 0.00
% 2.05/1.27  Index Matching       : 0.00
% 2.05/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
