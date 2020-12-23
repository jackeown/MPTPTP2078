%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:40 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 125 expanded)
%              Number of leaves         :   45 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 220 expanded)
%              Number of equality atoms :   50 (  93 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_56,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_107,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_82,c_107])).

tff(c_113,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_110])).

tff(c_86,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_84,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_191,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_195,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_191])).

tff(c_261,plain,(
    ! [B_163,A_164,C_165] :
      ( k1_xboole_0 = B_163
      | k1_relset_1(A_164,B_163,C_165) = A_164
      | ~ v1_funct_2(C_165,A_164,B_163)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_261])).

tff(c_267,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_195,c_264])).

tff(c_268,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_267])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_96,B_97,C_98,D_99] : k3_enumset1(A_96,A_96,B_97,C_98,D_99) = k2_enumset1(A_96,B_97,C_98,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [E_33,A_29,G_37,D_32,C_31] : r2_hidden(G_37,k3_enumset1(A_29,G_37,C_31,D_32,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_174,plain,(
    ! [A_103,B_104,C_105,D_106] : r2_hidden(A_103,k2_enumset1(A_103,B_104,C_105,D_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_24])).

tff(c_178,plain,(
    ! [A_107,B_108,C_109] : r2_hidden(A_107,k1_enumset1(A_107,B_108,C_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_174])).

tff(c_182,plain,(
    ! [A_110,B_111] : r2_hidden(A_110,k2_tarski(A_110,B_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_178])).

tff(c_185,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_276,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_185])).

tff(c_60,plain,(
    ! [B_48,A_47] :
      ( k1_tarski(k1_funct_1(B_48,A_47)) = k11_relat_1(B_48,A_47)
      | ~ r2_hidden(A_47,k1_relat_1(B_48))
      | ~ v1_funct_1(B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_286,plain,
    ( k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_276,c_60])).

tff(c_289,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) = k11_relat_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_86,c_286])).

tff(c_169,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_173,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_169])).

tff(c_78,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_209,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_78])).

tff(c_328,plain,(
    k11_relat_1('#skF_5','#skF_3') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_209])).

tff(c_54,plain,(
    ! [A_41,B_43] :
      ( k9_relat_1(A_41,k1_tarski(B_43)) = k11_relat_1(A_41,B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_368,plain,(
    ! [A_175] :
      ( k9_relat_1(A_175,k1_relat_1('#skF_5')) = k11_relat_1(A_175,'#skF_3')
      | ~ v1_relat_1(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_54])).

tff(c_58,plain,(
    ! [A_46] :
      ( k9_relat_1(A_46,k1_relat_1(A_46)) = k2_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_375,plain,
    ( k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_58])).

tff(c_385,plain,(
    k11_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_113,c_375])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.56  
% 2.63/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.56  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.63/1.56  
% 2.63/1.56  %Foreground sorts:
% 2.63/1.56  
% 2.63/1.56  
% 2.63/1.56  %Background operators:
% 2.63/1.56  
% 2.63/1.56  
% 2.63/1.56  %Foreground operators:
% 2.63/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.63/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.63/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.63/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.56  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.63/1.56  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.63/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.63/1.56  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.63/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.63/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.63/1.56  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.56  
% 3.01/1.57  tff(f_74, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.01/1.57  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.01/1.57  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.01/1.57  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.01/1.57  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.01/1.57  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.01/1.57  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.01/1.57  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.01/1.57  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.01/1.57  tff(f_60, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 3.01/1.57  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.01/1.57  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.01/1.57  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.01/1.57  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.01/1.57  tff(c_56, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.57  tff(c_82, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.01/1.57  tff(c_107, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.01/1.57  tff(c_110, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_82, c_107])).
% 3.01/1.57  tff(c_113, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_110])).
% 3.01/1.57  tff(c_86, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.01/1.57  tff(c_80, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.01/1.57  tff(c_84, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.01/1.57  tff(c_191, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.57  tff(c_195, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_191])).
% 3.01/1.57  tff(c_261, plain, (![B_163, A_164, C_165]: (k1_xboole_0=B_163 | k1_relset_1(A_164, B_163, C_165)=A_164 | ~v1_funct_2(C_165, A_164, B_163) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.01/1.57  tff(c_264, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_82, c_261])).
% 3.01/1.57  tff(c_267, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_195, c_264])).
% 3.01/1.57  tff(c_268, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_267])).
% 3.01/1.57  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.57  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.01/1.57  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.57  tff(c_145, plain, (![A_96, B_97, C_98, D_99]: (k3_enumset1(A_96, A_96, B_97, C_98, D_99)=k2_enumset1(A_96, B_97, C_98, D_99))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.57  tff(c_24, plain, (![E_33, A_29, G_37, D_32, C_31]: (r2_hidden(G_37, k3_enumset1(A_29, G_37, C_31, D_32, E_33)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.01/1.57  tff(c_174, plain, (![A_103, B_104, C_105, D_106]: (r2_hidden(A_103, k2_enumset1(A_103, B_104, C_105, D_106)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_24])).
% 3.01/1.57  tff(c_178, plain, (![A_107, B_108, C_109]: (r2_hidden(A_107, k1_enumset1(A_107, B_108, C_109)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_174])).
% 3.01/1.57  tff(c_182, plain, (![A_110, B_111]: (r2_hidden(A_110, k2_tarski(A_110, B_111)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_178])).
% 3.01/1.57  tff(c_185, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 3.01/1.57  tff(c_276, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_268, c_185])).
% 3.01/1.57  tff(c_60, plain, (![B_48, A_47]: (k1_tarski(k1_funct_1(B_48, A_47))=k11_relat_1(B_48, A_47) | ~r2_hidden(A_47, k1_relat_1(B_48)) | ~v1_funct_1(B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.57  tff(c_286, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_276, c_60])).
% 3.01/1.57  tff(c_289, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))=k11_relat_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_86, c_286])).
% 3.01/1.57  tff(c_169, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.01/1.57  tff(c_173, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_82, c_169])).
% 3.01/1.57  tff(c_78, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.01/1.57  tff(c_209, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_78])).
% 3.01/1.57  tff(c_328, plain, (k11_relat_1('#skF_5', '#skF_3')!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_209])).
% 3.01/1.57  tff(c_54, plain, (![A_41, B_43]: (k9_relat_1(A_41, k1_tarski(B_43))=k11_relat_1(A_41, B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.01/1.57  tff(c_368, plain, (![A_175]: (k9_relat_1(A_175, k1_relat_1('#skF_5'))=k11_relat_1(A_175, '#skF_3') | ~v1_relat_1(A_175))), inference(superposition, [status(thm), theory('equality')], [c_268, c_54])).
% 3.01/1.57  tff(c_58, plain, (![A_46]: (k9_relat_1(A_46, k1_relat_1(A_46))=k2_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.57  tff(c_375, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_368, c_58])).
% 3.01/1.57  tff(c_385, plain, (k11_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_113, c_375])).
% 3.01/1.57  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_328, c_385])).
% 3.01/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.57  
% 3.01/1.57  Inference rules
% 3.01/1.57  ----------------------
% 3.01/1.58  #Ref     : 0
% 3.01/1.58  #Sup     : 68
% 3.01/1.58  #Fact    : 0
% 3.01/1.58  #Define  : 0
% 3.01/1.58  #Split   : 0
% 3.01/1.58  #Chain   : 0
% 3.01/1.58  #Close   : 0
% 3.01/1.58  
% 3.01/1.58  Ordering : KBO
% 3.01/1.58  
% 3.01/1.58  Simplification rules
% 3.01/1.58  ----------------------
% 3.01/1.58  #Subsume      : 0
% 3.01/1.58  #Demod        : 24
% 3.01/1.58  #Tautology    : 45
% 3.01/1.58  #SimpNegUnit  : 4
% 3.01/1.58  #BackRed      : 6
% 3.01/1.58  
% 3.01/1.58  #Partial instantiations: 0
% 3.01/1.58  #Strategies tried      : 1
% 3.01/1.58  
% 3.01/1.58  Timing (in seconds)
% 3.01/1.58  ----------------------
% 3.01/1.58  Preprocessing        : 0.43
% 3.01/1.58  Parsing              : 0.22
% 3.01/1.58  CNF conversion       : 0.03
% 3.01/1.58  Main loop            : 0.25
% 3.01/1.58  Inferencing          : 0.08
% 3.01/1.58  Reduction            : 0.08
% 3.01/1.58  Demodulation         : 0.06
% 3.01/1.58  BG Simplification    : 0.02
% 3.01/1.58  Subsumption          : 0.06
% 3.01/1.58  Abstraction          : 0.02
% 3.01/1.58  MUC search           : 0.00
% 3.01/1.58  Cooper               : 0.00
% 3.01/1.58  Total                : 0.72
% 3.01/1.58  Index Insertion      : 0.00
% 3.01/1.58  Index Deletion       : 0.00
% 3.01/1.58  Index Matching       : 0.00
% 3.01/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
