%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:58 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 137 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 663 expanded)
%              Number of equality atoms :   95 ( 417 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_10,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_1'(A_4,B_5,C_6,D_22),A_4)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_3'(A_4,B_5,C_6,D_22),C_6)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( m1_subset_1('#skF_2'(A_4,B_5,C_6,D_22),B_5)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k3_mcart_1('#skF_1'(A_98,B_99,C_100,D_101),'#skF_2'(A_98,B_99,C_100,D_101),'#skF_3'(A_98,B_99,C_100,D_101)) = D_101
      | ~ m1_subset_1(D_101,k3_zfmisc_1(A_98,B_99,C_100))
      | k1_xboole_0 = C_100
      | k1_xboole_0 = B_99
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [F_51,G_55,H_57] :
      ( F_51 = '#skF_7'
      | k3_mcart_1(F_51,G_55,H_57) != '#skF_8'
      | ~ m1_subset_1(H_57,'#skF_6')
      | ~ m1_subset_1(G_55,'#skF_5')
      | ~ m1_subset_1(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_125,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( '#skF_1'(A_123,B_124,C_125,D_126) = '#skF_7'
      | D_126 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_123,B_124,C_125,D_126),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_123,B_124,C_125,D_126),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_123,B_124,C_125,D_126),'#skF_4')
      | ~ m1_subset_1(D_126,k3_zfmisc_1(A_123,B_124,C_125))
      | k1_xboole_0 = C_125
      | k1_xboole_0 = B_124
      | k1_xboole_0 = A_123 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_129,plain,(
    ! [A_4,C_6,D_22] :
      ( '#skF_1'(A_4,'#skF_5',C_6,D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_4,'#skF_5',C_6,D_22),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5',C_6,D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5',C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_8,c_125])).

tff(c_134,plain,(
    ! [A_127,C_128,D_129] :
      ( '#skF_1'(A_127,'#skF_5',C_128,D_129) = '#skF_7'
      | D_129 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_127,'#skF_5',C_128,D_129),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_127,'#skF_5',C_128,D_129),'#skF_4')
      | ~ m1_subset_1(D_129,k3_zfmisc_1(A_127,'#skF_5',C_128))
      | k1_xboole_0 = C_128
      | k1_xboole_0 = A_127 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_129])).

tff(c_138,plain,(
    ! [A_4,D_22] :
      ( '#skF_1'(A_4,'#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_4,'#skF_5','#skF_6',D_22),'#skF_4')
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_4 ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_143,plain,(
    ! [A_130,D_131] :
      ( '#skF_1'(A_130,'#skF_5','#skF_6',D_131) = '#skF_7'
      | D_131 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_130,'#skF_5','#skF_6',D_131),'#skF_4')
      | ~ m1_subset_1(D_131,k3_zfmisc_1(A_130,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_130 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_20,c_138])).

tff(c_147,plain,(
    ! [D_22] :
      ( '#skF_1'('#skF_4','#skF_5','#skF_6',D_22) = '#skF_7'
      | D_22 != '#skF_8'
      | ~ m1_subset_1(D_22,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10,c_143])).

tff(c_152,plain,(
    ! [D_132] :
      ( '#skF_1'('#skF_4','#skF_5','#skF_6',D_132) = '#skF_7'
      | D_132 != '#skF_8'
      | ~ m1_subset_1(D_132,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_24,c_147])).

tff(c_171,plain,(
    '#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_152])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_22] :
      ( k3_mcart_1('#skF_1'(A_4,B_5,C_6,D_22),'#skF_2'(A_4,B_5,C_6,D_22),'#skF_3'(A_4,B_5,C_6,D_22)) = D_22
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_4,B_5,C_6))
      | k1_xboole_0 = C_6
      | k1_xboole_0 = B_5
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_178,plain,
    ( k3_mcart_1('#skF_7','#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_4])).

tff(c_189,plain,
    ( k3_mcart_1('#skF_7','#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_178])).

tff(c_190,plain,(
    k3_mcart_1('#skF_7','#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_189])).

tff(c_16,plain,(
    ! [F_42,A_34,G_43,E_41,B_35,C_36] :
      ( k5_mcart_1(A_34,B_35,C_36,k3_mcart_1(E_41,F_42,G_43)) = E_41
      | k1_xboole_0 = C_36
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k3_mcart_1(E_41,F_42,G_43),k3_zfmisc_1(A_34,B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_228,plain,(
    ! [A_34,B_35,C_36] :
      ( k5_mcart_1(A_34,B_35,C_36,k3_mcart_1('#skF_7','#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'))) = '#skF_7'
      | k1_xboole_0 = C_36
      | k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_34,B_35,C_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_16])).

tff(c_250,plain,(
    ! [A_140,B_141,C_142] :
      ( k5_mcart_1(A_140,B_141,C_142,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_142
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_140
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_140,B_141,C_142)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_228])).

tff(c_256,plain,
    ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_250])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.16/1.29  
% 2.16/1.29  %Foreground sorts:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Background operators:
% 2.16/1.29  
% 2.16/1.29  
% 2.16/1.29  %Foreground operators:
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.29  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.29  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.16/1.29  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.29  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.16/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.29  
% 2.16/1.30  tff(f_98, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 2.16/1.30  tff(f_52, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.16/1.30  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.16/1.30  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_22, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_20, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_18, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_28, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_10, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_1'(A_4, B_5, C_6, D_22), A_4) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_6, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_3'(A_4, B_5, C_6, D_22), C_6) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_8, plain, (![A_4, B_5, C_6, D_22]: (m1_subset_1('#skF_2'(A_4, B_5, C_6, D_22), B_5) | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_80, plain, (![A_98, B_99, C_100, D_101]: (k3_mcart_1('#skF_1'(A_98, B_99, C_100, D_101), '#skF_2'(A_98, B_99, C_100, D_101), '#skF_3'(A_98, B_99, C_100, D_101))=D_101 | ~m1_subset_1(D_101, k3_zfmisc_1(A_98, B_99, C_100)) | k1_xboole_0=C_100 | k1_xboole_0=B_99 | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_26, plain, (![F_51, G_55, H_57]: (F_51='#skF_7' | k3_mcart_1(F_51, G_55, H_57)!='#skF_8' | ~m1_subset_1(H_57, '#skF_6') | ~m1_subset_1(G_55, '#skF_5') | ~m1_subset_1(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.16/1.30  tff(c_125, plain, (![A_123, B_124, C_125, D_126]: ('#skF_1'(A_123, B_124, C_125, D_126)='#skF_7' | D_126!='#skF_8' | ~m1_subset_1('#skF_3'(A_123, B_124, C_125, D_126), '#skF_6') | ~m1_subset_1('#skF_2'(A_123, B_124, C_125, D_126), '#skF_5') | ~m1_subset_1('#skF_1'(A_123, B_124, C_125, D_126), '#skF_4') | ~m1_subset_1(D_126, k3_zfmisc_1(A_123, B_124, C_125)) | k1_xboole_0=C_125 | k1_xboole_0=B_124 | k1_xboole_0=A_123)), inference(superposition, [status(thm), theory('equality')], [c_80, c_26])).
% 2.16/1.30  tff(c_129, plain, (![A_4, C_6, D_22]: ('#skF_1'(A_4, '#skF_5', C_6, D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_3'(A_4, '#skF_5', C_6, D_22), '#skF_6') | ~m1_subset_1('#skF_1'(A_4, '#skF_5', C_6, D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', C_6)) | k1_xboole_0=C_6 | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_8, c_125])).
% 2.16/1.30  tff(c_134, plain, (![A_127, C_128, D_129]: ('#skF_1'(A_127, '#skF_5', C_128, D_129)='#skF_7' | D_129!='#skF_8' | ~m1_subset_1('#skF_3'(A_127, '#skF_5', C_128, D_129), '#skF_6') | ~m1_subset_1('#skF_1'(A_127, '#skF_5', C_128, D_129), '#skF_4') | ~m1_subset_1(D_129, k3_zfmisc_1(A_127, '#skF_5', C_128)) | k1_xboole_0=C_128 | k1_xboole_0=A_127)), inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_129])).
% 2.16/1.30  tff(c_138, plain, (![A_4, D_22]: ('#skF_1'(A_4, '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1('#skF_1'(A_4, '#skF_5', '#skF_6', D_22), '#skF_4') | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_4)), inference(resolution, [status(thm)], [c_6, c_134])).
% 2.16/1.30  tff(c_143, plain, (![A_130, D_131]: ('#skF_1'(A_130, '#skF_5', '#skF_6', D_131)='#skF_7' | D_131!='#skF_8' | ~m1_subset_1('#skF_1'(A_130, '#skF_5', '#skF_6', D_131), '#skF_4') | ~m1_subset_1(D_131, k3_zfmisc_1(A_130, '#skF_5', '#skF_6')) | k1_xboole_0=A_130)), inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_20, c_138])).
% 2.16/1.30  tff(c_147, plain, (![D_22]: ('#skF_1'('#skF_4', '#skF_5', '#skF_6', D_22)='#skF_7' | D_22!='#skF_8' | ~m1_subset_1(D_22, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_10, c_143])).
% 2.16/1.30  tff(c_152, plain, (![D_132]: ('#skF_1'('#skF_4', '#skF_5', '#skF_6', D_132)='#skF_7' | D_132!='#skF_8' | ~m1_subset_1(D_132, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_24, c_147])).
% 2.16/1.30  tff(c_171, plain, ('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_28, c_152])).
% 2.16/1.30  tff(c_4, plain, (![A_4, B_5, C_6, D_22]: (k3_mcart_1('#skF_1'(A_4, B_5, C_6, D_22), '#skF_2'(A_4, B_5, C_6, D_22), '#skF_3'(A_4, B_5, C_6, D_22))=D_22 | ~m1_subset_1(D_22, k3_zfmisc_1(A_4, B_5, C_6)) | k1_xboole_0=C_6 | k1_xboole_0=B_5 | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.30  tff(c_178, plain, (k3_mcart_1('#skF_7', '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_171, c_4])).
% 2.16/1.30  tff(c_189, plain, (k3_mcart_1('#skF_7', '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_178])).
% 2.16/1.30  tff(c_190, plain, (k3_mcart_1('#skF_7', '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_189])).
% 2.16/1.30  tff(c_16, plain, (![F_42, A_34, G_43, E_41, B_35, C_36]: (k5_mcart_1(A_34, B_35, C_36, k3_mcart_1(E_41, F_42, G_43))=E_41 | k1_xboole_0=C_36 | k1_xboole_0=B_35 | k1_xboole_0=A_34 | ~m1_subset_1(k3_mcart_1(E_41, F_42, G_43), k3_zfmisc_1(A_34, B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.30  tff(c_228, plain, (![A_34, B_35, C_36]: (k5_mcart_1(A_34, B_35, C_36, k3_mcart_1('#skF_7', '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')))='#skF_7' | k1_xboole_0=C_36 | k1_xboole_0=B_35 | k1_xboole_0=A_34 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_34, B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_16])).
% 2.16/1.30  tff(c_250, plain, (![A_140, B_141, C_142]: (k5_mcart_1(A_140, B_141, C_142, '#skF_8')='#skF_7' | k1_xboole_0=C_142 | k1_xboole_0=B_141 | k1_xboole_0=A_140 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_140, B_141, C_142)))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_228])).
% 2.16/1.30  tff(c_256, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_250])).
% 2.16/1.30  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_256])).
% 2.16/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.30  
% 2.16/1.30  Inference rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Ref     : 0
% 2.16/1.30  #Sup     : 49
% 2.16/1.30  #Fact    : 0
% 2.16/1.30  #Define  : 0
% 2.16/1.30  #Split   : 0
% 2.16/1.30  #Chain   : 0
% 2.16/1.30  #Close   : 0
% 2.16/1.30  
% 2.16/1.30  Ordering : KBO
% 2.16/1.30  
% 2.16/1.30  Simplification rules
% 2.16/1.30  ----------------------
% 2.16/1.30  #Subsume      : 3
% 2.16/1.30  #Demod        : 24
% 2.16/1.30  #Tautology    : 16
% 2.16/1.30  #SimpNegUnit  : 8
% 2.16/1.30  #BackRed      : 0
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.31  Preprocessing        : 0.30
% 2.16/1.31  Parsing              : 0.16
% 2.16/1.31  CNF conversion       : 0.02
% 2.16/1.31  Main loop            : 0.23
% 2.16/1.31  Inferencing          : 0.09
% 2.16/1.31  Reduction            : 0.06
% 2.16/1.31  Demodulation         : 0.05
% 2.16/1.31  BG Simplification    : 0.02
% 2.16/1.31  Subsumption          : 0.05
% 2.16/1.31  Abstraction          : 0.02
% 2.16/1.31  MUC search           : 0.00
% 2.16/1.31  Cooper               : 0.00
% 2.16/1.31  Total                : 0.57
% 2.16/1.31  Index Insertion      : 0.00
% 2.16/1.31  Index Deletion       : 0.00
% 2.16/1.31  Index Matching       : 0.00
% 2.16/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
