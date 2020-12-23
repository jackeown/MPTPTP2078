%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:46 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   65 (  86 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   87 ( 124 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_22,plain,(
    ! [A_34] : m1_subset_1('#skF_1'(A_34),A_34) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_96,plain,(
    ! [A_69,C_70,B_71] :
      ( ~ r2_hidden(A_69,C_70)
      | ~ r1_xboole_0(k2_tarski(A_69,B_71),C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [A_69] : ~ r2_hidden(A_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_96])).

tff(c_26,plain,(
    ! [A_37] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [A_33] : k2_subset_1(A_33) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_36] : k3_subset_1(A_36,k1_subset_1(A_36)) = k2_subset_1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_53,plain,(
    ! [A_36] : k3_subset_1(A_36,k1_subset_1(A_36)) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_54,plain,(
    ! [A_36] : k3_subset_1(A_36,k1_xboole_0) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_53])).

tff(c_193,plain,(
    ! [C_103,A_104,B_105] :
      ( r2_hidden(C_103,k3_subset_1(A_104,B_105))
      | r2_hidden(C_103,B_105)
      | ~ m1_subset_1(C_103,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104))
      | k1_xboole_0 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_198,plain,(
    ! [C_103,A_36] :
      ( r2_hidden(C_103,A_36)
      | r2_hidden(C_103,k1_xboole_0)
      | ~ m1_subset_1(C_103,A_36)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36))
      | k1_xboole_0 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_193])).

tff(c_201,plain,(
    ! [C_103,A_36] :
      ( r2_hidden(C_103,A_36)
      | r2_hidden(C_103,k1_xboole_0)
      | ~ m1_subset_1(C_103,A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_198])).

tff(c_202,plain,(
    ! [C_103,A_36] :
      ( r2_hidden(C_103,A_36)
      | ~ m1_subset_1(C_103,A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_201])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_112,plain,(
    ! [A_76,C_77,B_78] :
      ( m1_subset_1(A_76,C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_120,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_112])).

tff(c_48,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_138,plain,(
    ! [A_88,B_89] :
      ( k7_setfam_1(A_88,k7_setfam_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_138])).

tff(c_148,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_140])).

tff(c_505,plain,(
    ! [A_154,D_155,B_156] :
      ( r2_hidden(k3_subset_1(A_154,D_155),B_156)
      | ~ r2_hidden(D_155,k7_setfam_1(A_154,B_156))
      | ~ m1_subset_1(D_155,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(k7_setfam_1(A_154,B_156),k1_zfmisc_1(k1_zfmisc_1(A_154)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k1_zfmisc_1(A_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_513,plain,(
    ! [D_155] :
      ( r2_hidden(k3_subset_1('#skF_3',D_155),k1_xboole_0)
      | ~ r2_hidden(D_155,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_155,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_505])).

tff(c_521,plain,(
    ! [D_155] :
      ( r2_hidden(k3_subset_1('#skF_3',D_155),k1_xboole_0)
      | ~ r2_hidden(D_155,'#skF_4')
      | ~ m1_subset_1(D_155,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_52,c_148,c_513])).

tff(c_525,plain,(
    ! [D_157] :
      ( ~ r2_hidden(D_157,'#skF_4')
      | ~ m1_subset_1(D_157,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_521])).

tff(c_560,plain,(
    ! [A_158] : ~ r2_hidden(A_158,'#skF_4') ),
    inference(resolution,[status(thm)],[c_120,c_525])).

tff(c_568,plain,(
    ! [C_103] :
      ( ~ m1_subset_1(C_103,'#skF_4')
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_202,c_560])).

tff(c_573,plain,(
    ! [C_159] : ~ m1_subset_1(C_159,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_568])).

tff(c_593,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_22,c_573])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.48  
% 2.91/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.48  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.91/1.48  
% 2.91/1.48  %Foreground sorts:
% 2.91/1.48  
% 2.91/1.48  
% 2.91/1.48  %Background operators:
% 2.91/1.48  
% 2.91/1.48  
% 2.91/1.48  %Foreground operators:
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.91/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.48  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.91/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.91/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.91/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.91/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.91/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.91/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.91/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.91/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.48  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.91/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.91/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.91/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.48  
% 2.91/1.49  tff(f_51, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.91/1.49  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.91/1.49  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.91/1.49  tff(f_44, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.91/1.49  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.91/1.49  tff(f_46, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.91/1.49  tff(f_48, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.91/1.49  tff(f_53, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.91/1.49  tff(f_69, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.91/1.49  tff(f_93, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.91/1.49  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.91/1.49  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.91/1.49  tff(c_22, plain, (![A_34]: (m1_subset_1('#skF_1'(A_34), A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.91/1.49  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.49  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.91/1.49  tff(c_96, plain, (![A_69, C_70, B_71]: (~r2_hidden(A_69, C_70) | ~r1_xboole_0(k2_tarski(A_69, B_71), C_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.91/1.49  tff(c_101, plain, (![A_69]: (~r2_hidden(A_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_96])).
% 2.91/1.49  tff(c_26, plain, (![A_37]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.49  tff(c_18, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.91/1.49  tff(c_20, plain, (![A_33]: (k2_subset_1(A_33)=A_33)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.91/1.49  tff(c_24, plain, (![A_36]: (k3_subset_1(A_36, k1_subset_1(A_36))=k2_subset_1(A_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.91/1.49  tff(c_53, plain, (![A_36]: (k3_subset_1(A_36, k1_subset_1(A_36))=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 2.91/1.49  tff(c_54, plain, (![A_36]: (k3_subset_1(A_36, k1_xboole_0)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_53])).
% 2.91/1.49  tff(c_193, plain, (![C_103, A_104, B_105]: (r2_hidden(C_103, k3_subset_1(A_104, B_105)) | r2_hidden(C_103, B_105) | ~m1_subset_1(C_103, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)) | k1_xboole_0=A_104)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.91/1.49  tff(c_198, plain, (![C_103, A_36]: (r2_hidden(C_103, A_36) | r2_hidden(C_103, k1_xboole_0) | ~m1_subset_1(C_103, A_36) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)) | k1_xboole_0=A_36)), inference(superposition, [status(thm), theory('equality')], [c_54, c_193])).
% 2.91/1.49  tff(c_201, plain, (![C_103, A_36]: (r2_hidden(C_103, A_36) | r2_hidden(C_103, k1_xboole_0) | ~m1_subset_1(C_103, A_36) | k1_xboole_0=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_198])).
% 2.91/1.49  tff(c_202, plain, (![C_103, A_36]: (r2_hidden(C_103, A_36) | ~m1_subset_1(C_103, A_36) | k1_xboole_0=A_36)), inference(negUnitSimplification, [status(thm)], [c_101, c_201])).
% 2.91/1.49  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.49  tff(c_112, plain, (![A_76, C_77, B_78]: (m1_subset_1(A_76, C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.91/1.49  tff(c_120, plain, (![A_76]: (m1_subset_1(A_76, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_112])).
% 2.91/1.49  tff(c_48, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.91/1.49  tff(c_138, plain, (![A_88, B_89]: (k7_setfam_1(A_88, k7_setfam_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.49  tff(c_140, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_52, c_138])).
% 2.91/1.49  tff(c_148, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_140])).
% 2.91/1.49  tff(c_505, plain, (![A_154, D_155, B_156]: (r2_hidden(k3_subset_1(A_154, D_155), B_156) | ~r2_hidden(D_155, k7_setfam_1(A_154, B_156)) | ~m1_subset_1(D_155, k1_zfmisc_1(A_154)) | ~m1_subset_1(k7_setfam_1(A_154, B_156), k1_zfmisc_1(k1_zfmisc_1(A_154))) | ~m1_subset_1(B_156, k1_zfmisc_1(k1_zfmisc_1(A_154))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.91/1.49  tff(c_513, plain, (![D_155]: (r2_hidden(k3_subset_1('#skF_3', D_155), k1_xboole_0) | ~r2_hidden(D_155, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_155, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_505])).
% 2.91/1.49  tff(c_521, plain, (![D_155]: (r2_hidden(k3_subset_1('#skF_3', D_155), k1_xboole_0) | ~r2_hidden(D_155, '#skF_4') | ~m1_subset_1(D_155, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_52, c_148, c_513])).
% 2.91/1.49  tff(c_525, plain, (![D_157]: (~r2_hidden(D_157, '#skF_4') | ~m1_subset_1(D_157, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_101, c_521])).
% 2.91/1.49  tff(c_560, plain, (![A_158]: (~r2_hidden(A_158, '#skF_4'))), inference(resolution, [status(thm)], [c_120, c_525])).
% 2.91/1.49  tff(c_568, plain, (![C_103]: (~m1_subset_1(C_103, '#skF_4') | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_202, c_560])).
% 2.91/1.49  tff(c_573, plain, (![C_159]: (~m1_subset_1(C_159, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_568])).
% 2.91/1.49  tff(c_593, plain, $false, inference(resolution, [status(thm)], [c_22, c_573])).
% 2.91/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.49  
% 2.91/1.49  Inference rules
% 2.91/1.49  ----------------------
% 2.91/1.49  #Ref     : 0
% 2.91/1.49  #Sup     : 120
% 2.91/1.49  #Fact    : 0
% 2.91/1.49  #Define  : 0
% 2.91/1.49  #Split   : 3
% 2.91/1.49  #Chain   : 0
% 2.91/1.49  #Close   : 0
% 2.91/1.49  
% 2.91/1.49  Ordering : KBO
% 2.91/1.49  
% 2.91/1.49  Simplification rules
% 2.91/1.49  ----------------------
% 2.91/1.49  #Subsume      : 28
% 2.91/1.49  #Demod        : 35
% 2.91/1.49  #Tautology    : 35
% 2.91/1.49  #SimpNegUnit  : 9
% 2.91/1.49  #BackRed      : 0
% 2.91/1.49  
% 2.91/1.49  #Partial instantiations: 0
% 2.91/1.49  #Strategies tried      : 1
% 2.91/1.49  
% 2.91/1.49  Timing (in seconds)
% 2.91/1.49  ----------------------
% 2.91/1.50  Preprocessing        : 0.35
% 2.91/1.50  Parsing              : 0.19
% 2.91/1.50  CNF conversion       : 0.02
% 2.91/1.50  Main loop            : 0.32
% 2.91/1.50  Inferencing          : 0.11
% 2.91/1.50  Reduction            : 0.10
% 2.91/1.50  Demodulation         : 0.07
% 2.91/1.50  BG Simplification    : 0.02
% 2.91/1.50  Subsumption          : 0.07
% 2.91/1.50  Abstraction          : 0.02
% 2.91/1.50  MUC search           : 0.00
% 2.91/1.50  Cooper               : 0.00
% 2.91/1.50  Total                : 0.70
% 2.91/1.50  Index Insertion      : 0.00
% 2.91/1.50  Index Deletion       : 0.00
% 2.91/1.50  Index Matching       : 0.00
% 2.91/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
