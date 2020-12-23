%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 165 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 441 expanded)
%              Number of equality atoms :   20 (  57 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_33,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [A_45,B_46,B_47] :
      ( m1_subset_1('#skF_1'(A_45,B_46),B_47)
      | ~ r1_tarski(A_45,B_47)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_125,c_16])).

tff(c_28,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_5')
      | ~ r2_hidden(D_17,'#skF_6')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_663,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_1'(A_89,B_90),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_89,B_90),'#skF_6')
      | ~ r1_tarski(A_89,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_153,c_28])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_691,plain,(
    ! [A_91] :
      ( ~ r2_hidden('#skF_1'(A_91,'#skF_5'),'#skF_6')
      | ~ r1_tarski(A_91,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_663,c_4])).

tff(c_707,plain,
    ( ~ r1_tarski('#skF_6',k1_zfmisc_1('#skF_4'))
    | r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_691])).

tff(c_717,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_707])).

tff(c_22,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_45,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_175,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),B_51)
      | r2_hidden('#skF_3'(A_50,B_51),A_50)
      | B_51 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_541,plain,(
    ! [A_80,B_81,B_82] :
      ( r2_hidden('#skF_3'(A_80,B_81),B_82)
      | ~ r1_tarski(A_80,B_82)
      | r2_hidden('#skF_2'(A_80,B_81),B_81)
      | B_81 = A_80 ) ),
    inference(resolution,[status(thm)],[c_175,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_580,plain,(
    ! [A_80,B_82] :
      ( ~ r1_tarski(A_80,B_82)
      | r2_hidden('#skF_2'(A_80,B_82),B_82)
      | B_82 = A_80 ) ),
    inference(resolution,[status(thm)],[c_541,c_10])).

tff(c_590,plain,(
    ! [A_83,B_84] :
      ( ~ r1_tarski(A_83,B_84)
      | r2_hidden('#skF_2'(A_83,B_84),B_84)
      | B_84 = A_83 ) ),
    inference(resolution,[status(thm)],[c_541,c_10])).

tff(c_842,plain,(
    ! [A_103,B_104,B_105] :
      ( r2_hidden('#skF_2'(A_103,B_104),B_105)
      | ~ r1_tarski(B_104,B_105)
      | ~ r1_tarski(A_103,B_104)
      | B_104 = A_103 ) ),
    inference(resolution,[status(thm)],[c_590,c_2])).

tff(c_1368,plain,(
    ! [A_154,B_155,B_156] :
      ( m1_subset_1('#skF_2'(A_154,B_155),B_156)
      | ~ r1_tarski(B_155,B_156)
      | ~ r1_tarski(A_154,B_155)
      | B_155 = A_154 ) ),
    inference(resolution,[status(thm)],[c_842,c_16])).

tff(c_30,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_6')
      | ~ r2_hidden(D_17,'#skF_5')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1699,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_2'(A_179,B_180),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_179,B_180),'#skF_5')
      | ~ r1_tarski(B_180,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_179,B_180)
      | B_180 = A_179 ) ),
    inference(resolution,[status(thm)],[c_1368,c_30])).

tff(c_1718,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_2'(A_80,'#skF_5'),'#skF_6')
      | ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(A_80,'#skF_5')
      | A_80 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_580,c_1699])).

tff(c_1747,plain,(
    ! [A_181] :
      ( r2_hidden('#skF_2'(A_181,'#skF_5'),'#skF_6')
      | ~ r1_tarski(A_181,'#skF_5')
      | A_181 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_1718])).

tff(c_210,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_2'(A_52,B_53),A_52)
      | r2_hidden('#skF_3'(A_52,B_53),A_52)
      | B_53 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_232,plain,(
    ! [A_52,B_53,B_2] :
      ( r2_hidden('#skF_3'(A_52,B_53),B_2)
      | ~ r1_tarski(A_52,B_2)
      | ~ r2_hidden('#skF_2'(A_52,B_53),A_52)
      | B_53 = A_52 ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_1750,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5'),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | ~ r1_tarski('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1747,c_232])).

tff(c_1770,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5'),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | '#skF_5' = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_1750])).

tff(c_1904,plain,(
    ! [B_184] :
      ( r2_hidden('#skF_3'('#skF_6','#skF_5'),B_184)
      | ~ r1_tarski('#skF_6',B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1770])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1759,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1747,c_8])).

tff(c_1779,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_1759])).

tff(c_1780,plain,(
    ~ r2_hidden('#skF_3'('#skF_6','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1779])).

tff(c_1907,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_1904,c_1780])).

tff(c_1935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_1907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.70  
% 4.11/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.70  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.11/1.70  
% 4.11/1.70  %Foreground sorts:
% 4.11/1.70  
% 4.11/1.70  
% 4.11/1.70  %Background operators:
% 4.11/1.70  
% 4.11/1.70  
% 4.11/1.70  %Foreground operators:
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.11/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.70  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.11/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.70  
% 4.11/1.72  tff(f_62, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 4.11/1.72  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.11/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.11/1.72  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.11/1.72  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.11/1.72  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_33, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.11/1.72  tff(c_44, plain, (r1_tarski('#skF_6', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_33])).
% 4.11/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.72  tff(c_75, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.72  tff(c_125, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_1'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_75])).
% 4.11/1.72  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.11/1.72  tff(c_153, plain, (![A_45, B_46, B_47]: (m1_subset_1('#skF_1'(A_45, B_46), B_47) | ~r1_tarski(A_45, B_47) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_125, c_16])).
% 4.11/1.72  tff(c_28, plain, (![D_17]: (r2_hidden(D_17, '#skF_5') | ~r2_hidden(D_17, '#skF_6') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_663, plain, (![A_89, B_90]: (r2_hidden('#skF_1'(A_89, B_90), '#skF_5') | ~r2_hidden('#skF_1'(A_89, B_90), '#skF_6') | ~r1_tarski(A_89, k1_zfmisc_1('#skF_4')) | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_153, c_28])).
% 4.11/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.72  tff(c_691, plain, (![A_91]: (~r2_hidden('#skF_1'(A_91, '#skF_5'), '#skF_6') | ~r1_tarski(A_91, k1_zfmisc_1('#skF_4')) | r1_tarski(A_91, '#skF_5'))), inference(resolution, [status(thm)], [c_663, c_4])).
% 4.11/1.72  tff(c_707, plain, (~r1_tarski('#skF_6', k1_zfmisc_1('#skF_4')) | r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_691])).
% 4.11/1.72  tff(c_717, plain, (r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_707])).
% 4.11/1.72  tff(c_22, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_45, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_33])).
% 4.11/1.72  tff(c_175, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), B_51) | r2_hidden('#skF_3'(A_50, B_51), A_50) | B_51=A_50)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.72  tff(c_541, plain, (![A_80, B_81, B_82]: (r2_hidden('#skF_3'(A_80, B_81), B_82) | ~r1_tarski(A_80, B_82) | r2_hidden('#skF_2'(A_80, B_81), B_81) | B_81=A_80)), inference(resolution, [status(thm)], [c_175, c_2])).
% 4.11/1.72  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.72  tff(c_580, plain, (![A_80, B_82]: (~r1_tarski(A_80, B_82) | r2_hidden('#skF_2'(A_80, B_82), B_82) | B_82=A_80)), inference(resolution, [status(thm)], [c_541, c_10])).
% 4.11/1.72  tff(c_590, plain, (![A_83, B_84]: (~r1_tarski(A_83, B_84) | r2_hidden('#skF_2'(A_83, B_84), B_84) | B_84=A_83)), inference(resolution, [status(thm)], [c_541, c_10])).
% 4.11/1.72  tff(c_842, plain, (![A_103, B_104, B_105]: (r2_hidden('#skF_2'(A_103, B_104), B_105) | ~r1_tarski(B_104, B_105) | ~r1_tarski(A_103, B_104) | B_104=A_103)), inference(resolution, [status(thm)], [c_590, c_2])).
% 4.11/1.72  tff(c_1368, plain, (![A_154, B_155, B_156]: (m1_subset_1('#skF_2'(A_154, B_155), B_156) | ~r1_tarski(B_155, B_156) | ~r1_tarski(A_154, B_155) | B_155=A_154)), inference(resolution, [status(thm)], [c_842, c_16])).
% 4.11/1.72  tff(c_30, plain, (![D_17]: (r2_hidden(D_17, '#skF_6') | ~r2_hidden(D_17, '#skF_5') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.72  tff(c_1699, plain, (![A_179, B_180]: (r2_hidden('#skF_2'(A_179, B_180), '#skF_6') | ~r2_hidden('#skF_2'(A_179, B_180), '#skF_5') | ~r1_tarski(B_180, k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_179, B_180) | B_180=A_179)), inference(resolution, [status(thm)], [c_1368, c_30])).
% 4.11/1.72  tff(c_1718, plain, (![A_80]: (r2_hidden('#skF_2'(A_80, '#skF_5'), '#skF_6') | ~r1_tarski('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski(A_80, '#skF_5') | A_80='#skF_5')), inference(resolution, [status(thm)], [c_580, c_1699])).
% 4.11/1.72  tff(c_1747, plain, (![A_181]: (r2_hidden('#skF_2'(A_181, '#skF_5'), '#skF_6') | ~r1_tarski(A_181, '#skF_5') | A_181='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_1718])).
% 4.11/1.72  tff(c_210, plain, (![A_52, B_53]: (~r2_hidden('#skF_2'(A_52, B_53), A_52) | r2_hidden('#skF_3'(A_52, B_53), A_52) | B_53=A_52)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.72  tff(c_232, plain, (![A_52, B_53, B_2]: (r2_hidden('#skF_3'(A_52, B_53), B_2) | ~r1_tarski(A_52, B_2) | ~r2_hidden('#skF_2'(A_52, B_53), A_52) | B_53=A_52)), inference(resolution, [status(thm)], [c_210, c_2])).
% 4.11/1.72  tff(c_1750, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_6', '#skF_5'), B_2) | ~r1_tarski('#skF_6', B_2) | ~r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6')), inference(resolution, [status(thm)], [c_1747, c_232])).
% 4.11/1.72  tff(c_1770, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_6', '#skF_5'), B_2) | ~r1_tarski('#skF_6', B_2) | '#skF_5'='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_1750])).
% 4.11/1.72  tff(c_1904, plain, (![B_184]: (r2_hidden('#skF_3'('#skF_6', '#skF_5'), B_184) | ~r1_tarski('#skF_6', B_184))), inference(negUnitSimplification, [status(thm)], [c_22, c_1770])).
% 4.11/1.72  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.11/1.72  tff(c_1759, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5') | ~r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1747, c_8])).
% 4.11/1.72  tff(c_1779, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_717, c_1759])).
% 4.11/1.72  tff(c_1780, plain, (~r2_hidden('#skF_3'('#skF_6', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_22, c_1779])).
% 4.11/1.72  tff(c_1907, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_1904, c_1780])).
% 4.11/1.72  tff(c_1935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_717, c_1907])).
% 4.11/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.72  
% 4.11/1.72  Inference rules
% 4.11/1.72  ----------------------
% 4.11/1.72  #Ref     : 0
% 4.11/1.72  #Sup     : 387
% 4.11/1.72  #Fact    : 0
% 4.11/1.72  #Define  : 0
% 4.11/1.72  #Split   : 4
% 4.11/1.72  #Chain   : 0
% 4.11/1.72  #Close   : 0
% 4.11/1.72  
% 4.11/1.72  Ordering : KBO
% 4.11/1.72  
% 4.11/1.72  Simplification rules
% 4.11/1.72  ----------------------
% 4.11/1.72  #Subsume      : 64
% 4.11/1.72  #Demod        : 76
% 4.11/1.72  #Tautology    : 64
% 4.11/1.72  #SimpNegUnit  : 9
% 4.11/1.72  #BackRed      : 0
% 4.11/1.72  
% 4.11/1.72  #Partial instantiations: 0
% 4.11/1.72  #Strategies tried      : 1
% 4.11/1.72  
% 4.11/1.72  Timing (in seconds)
% 4.11/1.72  ----------------------
% 4.11/1.72  Preprocessing        : 0.29
% 4.11/1.72  Parsing              : 0.15
% 4.11/1.72  CNF conversion       : 0.02
% 4.11/1.72  Main loop            : 0.67
% 4.11/1.72  Inferencing          : 0.26
% 4.11/1.72  Reduction            : 0.17
% 4.11/1.72  Demodulation         : 0.11
% 4.11/1.72  BG Simplification    : 0.02
% 4.11/1.72  Subsumption          : 0.17
% 4.11/1.72  Abstraction          : 0.03
% 4.11/1.72  MUC search           : 0.00
% 4.11/1.72  Cooper               : 0.00
% 4.11/1.72  Total                : 0.99
% 4.11/1.72  Index Insertion      : 0.00
% 4.11/1.72  Index Deletion       : 0.00
% 4.11/1.72  Index Matching       : 0.00
% 4.11/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
