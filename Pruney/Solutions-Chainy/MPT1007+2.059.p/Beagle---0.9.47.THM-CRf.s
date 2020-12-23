%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:19 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 159 expanded)
%              Number of leaves         :   42 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  124 ( 338 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_97,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_97])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    ! [A_38,B_41] :
      ( k1_funct_1(A_38,B_41) = k1_xboole_0
      | r2_hidden(B_41,k1_relat_1(A_38))
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_203,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_212,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_203])).

tff(c_239,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1(k2_relset_1(A_117,B_118,C_119),k1_zfmisc_1(B_118))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_257,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_239])).

tff(c_263,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_257])).

tff(c_328,plain,(
    ! [B_139,A_140] :
      ( r2_hidden(k1_funct_1(B_139,A_140),k2_relat_1(B_139))
      | ~ r2_hidden(A_140,k1_relat_1(B_139))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [C_35,A_32,B_33] :
      ( r2_hidden(C_35,A_32)
      | ~ r2_hidden(C_35,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_776,plain,(
    ! [B_220,A_221,A_222] :
      ( r2_hidden(k1_funct_1(B_220,A_221),A_222)
      | ~ m1_subset_1(k2_relat_1(B_220),k1_zfmisc_1(A_222))
      | ~ r2_hidden(A_221,k1_relat_1(B_220))
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_328,c_22])).

tff(c_778,plain,(
    ! [A_221] :
      ( r2_hidden(k1_funct_1('#skF_3',A_221),'#skF_2')
      | ~ r2_hidden(A_221,k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_263,c_776])).

tff(c_786,plain,(
    ! [A_223] :
      ( r2_hidden(k1_funct_1('#skF_3',A_223),'#skF_2')
      | ~ r2_hidden(A_223,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68,c_778])).

tff(c_60,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_793,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_786,c_60])).

tff(c_796,plain,
    ( k1_funct_1('#skF_3','#skF_1') = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_793])).

tff(c_799,plain,(
    k1_funct_1('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68,c_796])).

tff(c_800,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_60])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_169,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_178,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_169])).

tff(c_564,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_575,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_564])).

tff(c_580,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_178,c_575])).

tff(c_581,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_580])).

tff(c_38,plain,(
    ! [B_46,A_45] :
      ( k1_tarski(k1_funct_1(B_46,A_45)) = k2_relat_1(B_46)
      | k1_tarski(A_45) != k1_relat_1(B_46)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_813,plain,
    ( k2_relat_1('#skF_3') = k1_tarski(k1_xboole_0)
    | k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_38])).

tff(c_821,plain,(
    k2_relat_1('#skF_3') = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_68,c_581,c_813])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_267,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_263,c_24])).

tff(c_824,plain,(
    r1_tarski(k1_tarski(k1_xboole_0),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_267])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_113,plain,(
    ! [A_75,C_76,B_77] :
      ( r2_hidden(A_75,C_76)
      | ~ r1_tarski(k2_tarski(A_75,B_77),C_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_1,C_76] :
      ( r2_hidden(A_1,C_76)
      | ~ r1_tarski(k1_tarski(A_1),C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_841,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_824,c_116])).

tff(c_845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_800,c_841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.52  
% 3.29/1.52  %Foreground sorts:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Background operators:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Foreground operators:
% 3.29/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.29/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.29/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.29/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.29/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.52  
% 3.29/1.53  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.29/1.53  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.53  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.29/1.53  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.29/1.53  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.29/1.53  tff(f_82, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.29/1.53  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.29/1.53  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.53  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.29/1.53  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.29/1.53  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.53  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.53  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.29/1.53  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.53  tff(c_97, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.53  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_97])).
% 3.29/1.53  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.53  tff(c_34, plain, (![A_38, B_41]: (k1_funct_1(A_38, B_41)=k1_xboole_0 | r2_hidden(B_41, k1_relat_1(A_38)) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.29/1.53  tff(c_203, plain, (![A_109, B_110, C_111]: (k2_relset_1(A_109, B_110, C_111)=k2_relat_1(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.29/1.53  tff(c_212, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_203])).
% 3.29/1.53  tff(c_239, plain, (![A_117, B_118, C_119]: (m1_subset_1(k2_relset_1(A_117, B_118, C_119), k1_zfmisc_1(B_118)) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.29/1.53  tff(c_257, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_212, c_239])).
% 3.29/1.53  tff(c_263, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_257])).
% 3.29/1.53  tff(c_328, plain, (![B_139, A_140]: (r2_hidden(k1_funct_1(B_139, A_140), k2_relat_1(B_139)) | ~r2_hidden(A_140, k1_relat_1(B_139)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.29/1.53  tff(c_22, plain, (![C_35, A_32, B_33]: (r2_hidden(C_35, A_32) | ~r2_hidden(C_35, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.53  tff(c_776, plain, (![B_220, A_221, A_222]: (r2_hidden(k1_funct_1(B_220, A_221), A_222) | ~m1_subset_1(k2_relat_1(B_220), k1_zfmisc_1(A_222)) | ~r2_hidden(A_221, k1_relat_1(B_220)) | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(resolution, [status(thm)], [c_328, c_22])).
% 3.29/1.53  tff(c_778, plain, (![A_221]: (r2_hidden(k1_funct_1('#skF_3', A_221), '#skF_2') | ~r2_hidden(A_221, k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_263, c_776])).
% 3.29/1.53  tff(c_786, plain, (![A_223]: (r2_hidden(k1_funct_1('#skF_3', A_223), '#skF_2') | ~r2_hidden(A_223, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68, c_778])).
% 3.29/1.53  tff(c_60, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.53  tff(c_793, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_786, c_60])).
% 3.29/1.53  tff(c_796, plain, (k1_funct_1('#skF_3', '#skF_1')=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_793])).
% 3.29/1.53  tff(c_799, plain, (k1_funct_1('#skF_3', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68, c_796])).
% 3.29/1.53  tff(c_800, plain, (~r2_hidden(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_60])).
% 3.29/1.53  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.53  tff(c_66, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.53  tff(c_169, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.29/1.53  tff(c_178, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_169])).
% 3.29/1.53  tff(c_564, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.53  tff(c_575, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_64, c_564])).
% 3.29/1.53  tff(c_580, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_178, c_575])).
% 3.29/1.53  tff(c_581, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_580])).
% 3.29/1.53  tff(c_38, plain, (![B_46, A_45]: (k1_tarski(k1_funct_1(B_46, A_45))=k2_relat_1(B_46) | k1_tarski(A_45)!=k1_relat_1(B_46) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.53  tff(c_813, plain, (k2_relat_1('#skF_3')=k1_tarski(k1_xboole_0) | k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_799, c_38])).
% 3.29/1.53  tff(c_821, plain, (k2_relat_1('#skF_3')=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_68, c_581, c_813])).
% 3.29/1.53  tff(c_24, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/1.53  tff(c_267, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_263, c_24])).
% 3.29/1.53  tff(c_824, plain, (r1_tarski(k1_tarski(k1_xboole_0), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_267])).
% 3.29/1.53  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.53  tff(c_113, plain, (![A_75, C_76, B_77]: (r2_hidden(A_75, C_76) | ~r1_tarski(k2_tarski(A_75, B_77), C_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.53  tff(c_116, plain, (![A_1, C_76]: (r2_hidden(A_1, C_76) | ~r1_tarski(k1_tarski(A_1), C_76))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 3.29/1.53  tff(c_841, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_824, c_116])).
% 3.29/1.53  tff(c_845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_800, c_841])).
% 3.29/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.53  
% 3.29/1.53  Inference rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Ref     : 0
% 3.29/1.53  #Sup     : 162
% 3.29/1.53  #Fact    : 0
% 3.29/1.53  #Define  : 0
% 3.29/1.53  #Split   : 1
% 3.29/1.53  #Chain   : 0
% 3.29/1.53  #Close   : 0
% 3.29/1.53  
% 3.29/1.53  Ordering : KBO
% 3.29/1.53  
% 3.29/1.53  Simplification rules
% 3.29/1.53  ----------------------
% 3.29/1.53  #Subsume      : 10
% 3.29/1.53  #Demod        : 62
% 3.29/1.53  #Tautology    : 59
% 3.29/1.53  #SimpNegUnit  : 8
% 3.29/1.53  #BackRed      : 9
% 3.29/1.53  
% 3.29/1.53  #Partial instantiations: 0
% 3.29/1.53  #Strategies tried      : 1
% 3.29/1.53  
% 3.29/1.53  Timing (in seconds)
% 3.29/1.53  ----------------------
% 3.29/1.53  Preprocessing        : 0.35
% 3.29/1.54  Parsing              : 0.18
% 3.29/1.54  CNF conversion       : 0.02
% 3.29/1.54  Main loop            : 0.36
% 3.29/1.54  Inferencing          : 0.14
% 3.29/1.54  Reduction            : 0.11
% 3.29/1.54  Demodulation         : 0.07
% 3.29/1.54  BG Simplification    : 0.03
% 3.29/1.54  Subsumption          : 0.06
% 3.29/1.54  Abstraction          : 0.02
% 3.29/1.54  MUC search           : 0.00
% 3.29/1.54  Cooper               : 0.00
% 3.29/1.54  Total                : 0.75
% 3.29/1.54  Index Insertion      : 0.00
% 3.29/1.54  Index Deletion       : 0.00
% 3.29/1.54  Index Matching       : 0.00
% 3.29/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
