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
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  137 (1067 expanded)
%              Number of leaves         :   41 ( 417 expanded)
%              Depth                    :   15
%              Number of atoms          :  432 (4647 expanded)
%              Number of equality atoms :    4 ( 108 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_eqrel_1,type,(
    k8_eqrel_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(m1_eqrel_1,type,(
    m1_eqrel_1: ( $i * $i ) > $o )).

tff(k7_eqrel_1,type,(
    k7_eqrel_1: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k9_eqrel_1,type,(
    k9_eqrel_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_binop_1,type,(
    r3_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(r1_binop_1,type,(
    r1_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k3_filter_1,type,(
    k3_filter_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(m2_filter_1,type,(
    m2_filter_1: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_binop_1,type,(
    r2_binop_1: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_221,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_partfun1(B,A)
              & v3_relat_2(B)
              & v8_relat_2(B)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( m2_filter_1(D,A,B)
                   => ( r3_binop_1(A,C,D)
                     => r3_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_filter_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r3_binop_1(A,B,C)
          <=> ( r1_binop_1(A,B,C)
              & r2_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_binop_1)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_176,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r1_binop_1(A,C,D)
                   => r1_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_filter_1)).

tff(f_198,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( m1_subset_1(C,A)
             => ! [D] :
                  ( m2_filter_1(D,A,B)
                 => ( r2_binop_1(A,C,D)
                   => r2_binop_1(k8_eqrel_1(A,B),k9_eqrel_1(A,B,C),k3_filter_1(A,B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_filter_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ~ v1_xboole_0(k7_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_eqrel_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_eqrel_1(B,A)
     => m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v1_partfun1(B,A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & v1_funct_1(C)
        & v1_funct_2(C,k2_zfmisc_1(A,A),A)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
     => ( v1_funct_1(k3_filter_1(A,B,C))
        & v1_funct_2(k3_filter_1(A,B,C),k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B))
        & m1_subset_1(k3_filter_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_filter_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_46,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_70,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_75,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_funct_1(C_81)
      | ~ m2_filter_1(C_81,A_82,B_83)
      | ~ v1_relat_1(B_83)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_78,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_81,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_78])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_81])).

tff(c_84,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_funct_2(C_86,k2_zfmisc_1(A_87,A_87),A_87)
      | ~ m2_filter_1(C_86,A_87,B_88)
      | ~ v1_relat_1(B_88)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_86,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_84])).

tff(c_89,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86])).

tff(c_90,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_89])).

tff(c_102,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_96,A_96),A_96)))
      | ~ m2_filter_1(C_95,A_96,B_97)
      | ~ v1_relat_1(B_97)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_104,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_102])).

tff(c_107,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_104])).

tff(c_108,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_107])).

tff(c_44,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_155,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_binop_1(A_107,B_108,C_109)
      | ~ r3_binop_1(A_107,B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_107,A_107),A_107)))
      | ~ v1_funct_2(C_109,k2_zfmisc_1(A_107,A_107),A_107)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(B_108,A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_157,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_155])).

tff(c_160,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_82,c_90,c_108,c_157])).

tff(c_56,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_54,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_52,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_132,plain,(
    ! [A_103,B_104] :
      ( k8_eqrel_1(A_103,B_104) = k7_eqrel_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v1_partfun1(B_104,A_103)
      | ~ v8_relat_2(B_104)
      | ~ v3_relat_2(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_135,plain,
    ( k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_132])).

tff(c_138,plain,(
    k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_135])).

tff(c_238,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( r1_binop_1(k8_eqrel_1(A_126,B_127),k9_eqrel_1(A_126,B_127,C_128),k3_filter_1(A_126,B_127,D_129))
      | ~ r1_binop_1(A_126,C_128,D_129)
      | ~ m2_filter_1(D_129,A_126,B_127)
      | ~ m1_subset_1(C_128,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1(A_126,A_126)))
      | ~ v8_relat_2(B_127)
      | ~ v3_relat_2(B_127)
      | ~ v1_partfun1(B_127,A_126)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_241,plain,(
    ! [C_128,D_129] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_128),k3_filter_1('#skF_1','#skF_2',D_129))
      | ~ r1_binop_1('#skF_1',C_128,D_129)
      | ~ m2_filter_1(D_129,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_128,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_238])).

tff(c_243,plain,(
    ! [C_128,D_129] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_128),k3_filter_1('#skF_1','#skF_2',D_129))
      | ~ r1_binop_1('#skF_1',C_128,D_129)
      | ~ m2_filter_1(D_129,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_128,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_241])).

tff(c_244,plain,(
    ! [C_128,D_129] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_128),k3_filter_1('#skF_1','#skF_2',D_129))
      | ~ r1_binop_1('#skF_1',C_128,D_129)
      | ~ m2_filter_1(D_129,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_128,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_243])).

tff(c_161,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_binop_1(A_110,B_111,C_112)
      | ~ r3_binop_1(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_110,A_110),A_110)))
      | ~ v1_funct_2(C_112,k2_zfmisc_1(A_110,A_110),A_110)
      | ~ v1_funct_1(C_112)
      | ~ m1_subset_1(B_111,A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_163,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_166,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_82,c_90,c_108,c_163])).

tff(c_253,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( r2_binop_1(k8_eqrel_1(A_133,B_134),k9_eqrel_1(A_133,B_134,C_135),k3_filter_1(A_133,B_134,D_136))
      | ~ r2_binop_1(A_133,C_135,D_136)
      | ~ m2_filter_1(D_136,A_133,B_134)
      | ~ m1_subset_1(C_135,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_zfmisc_1(A_133,A_133)))
      | ~ v8_relat_2(B_134)
      | ~ v3_relat_2(B_134)
      | ~ v1_partfun1(B_134,A_133)
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_256,plain,(
    ! [C_135,D_136] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_135),k3_filter_1('#skF_1','#skF_2',D_136))
      | ~ r2_binop_1('#skF_1',C_135,D_136)
      | ~ m2_filter_1(D_136,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_135,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_253])).

tff(c_258,plain,(
    ! [C_135,D_136] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_135),k3_filter_1('#skF_1','#skF_2',D_136))
      | ~ r2_binop_1('#skF_1',C_135,D_136)
      | ~ m2_filter_1(D_136,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_135,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_256])).

tff(c_259,plain,(
    ! [C_135,D_136] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_135),k3_filter_1('#skF_1','#skF_2',D_136))
      | ~ r2_binop_1('#skF_1',C_135,D_136)
      | ~ m2_filter_1(D_136,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_135,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_258])).

tff(c_145,plain,(
    ! [A_105,B_106] :
      ( ~ v1_xboole_0(k7_eqrel_1(A_105,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_zfmisc_1(A_105,A_105)))
      | ~ v1_partfun1(B_106,A_105)
      | ~ v8_relat_2(B_106)
      | ~ v3_relat_2(B_106)
      | v1_xboole_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_148,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_145])).

tff(c_151,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_148])).

tff(c_152,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_151])).

tff(c_109,plain,(
    ! [A_98,B_99] :
      ( m1_eqrel_1(k8_eqrel_1(A_98,B_99),A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v1_partfun1(B_99,A_98)
      | ~ v8_relat_2(B_99)
      | ~ v3_relat_2(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_112,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_115,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_112])).

tff(c_139,plain,(
    m1_eqrel_1(k7_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_115])).

tff(c_26,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23)))
      | ~ m1_eqrel_1(B_24,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_167,plain,(
    ! [A_113,B_114,C_115] :
      ( m2_subset_1(k9_eqrel_1(A_113,B_114,C_115),k1_zfmisc_1(A_113),k8_eqrel_1(A_113,B_114))
      | ~ m1_subset_1(C_115,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_zfmisc_1(A_113,A_113)))
      | ~ v1_partfun1(B_114,A_113)
      | ~ v8_relat_2(B_114)
      | ~ v3_relat_2(B_114)
      | v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_172,plain,(
    ! [C_115] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_115),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_115,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_partfun1('#skF_2','#skF_1')
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_167])).

tff(c_175,plain,(
    ! [C_115] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_115),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_115,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_50,c_172])).

tff(c_183,plain,(
    ! [C_119] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_119),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_175])).

tff(c_6,plain,(
    ! [C_10,B_8,A_7] :
      ( m1_subset_1(C_10,B_8)
      | ~ m2_subset_1(C_10,A_7,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7))
      | v1_xboole_0(B_8)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_185,plain,(
    ! [C_119] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_119),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_119,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_183,c_6])).

tff(c_188,plain,(
    ! [C_119] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_119),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_185])).

tff(c_200,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_203,plain,(
    ~ m1_eqrel_1(k7_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_200])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_203])).

tff(c_209,plain,(
    m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_220,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_214])).

tff(c_208,plain,(
    ! [C_119] :
      ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_119),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_119,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_221,plain,(
    ! [C_119] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_119),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_119,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_208])).

tff(c_231,plain,(
    ! [A_123,B_124,C_125] :
      ( v1_funct_1(k3_filter_1(A_123,B_124,C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_123,A_123),A_123)))
      | ~ v1_funct_2(C_125,k2_zfmisc_1(A_123,A_123),A_123)
      | ~ v1_funct_1(C_125)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1(A_123,A_123)))
      | ~ v8_relat_2(B_124)
      | ~ v3_relat_2(B_124)
      | ~ v1_partfun1(B_124,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_233,plain,(
    ! [B_124] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_124,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_124)
      | ~ v3_relat_2(B_124)
      | ~ v1_partfun1(B_124,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_108,c_231])).

tff(c_236,plain,(
    ! [B_124] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_124,'#skF_4'))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_124)
      | ~ v3_relat_2(B_124)
      | ~ v1_partfun1(B_124,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_90,c_233])).

tff(c_245,plain,(
    ! [B_130] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_130,'#skF_4'))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_130)
      | ~ v3_relat_2(B_130)
      | ~ v1_partfun1(B_130,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_236])).

tff(c_248,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_245])).

tff(c_251,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_248])).

tff(c_278,plain,(
    ! [A_145,B_146,C_147] :
      ( v1_funct_2(k3_filter_1(A_145,B_146,C_147),k2_zfmisc_1(k8_eqrel_1(A_145,B_146),k8_eqrel_1(A_145,B_146)),k8_eqrel_1(A_145,B_146))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_145,A_145),A_145)))
      | ~ v1_funct_2(C_147,k2_zfmisc_1(A_145,A_145),A_145)
      | ~ v1_funct_1(C_147)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(k2_zfmisc_1(A_145,A_145)))
      | ~ v8_relat_2(B_146)
      | ~ v3_relat_2(B_146)
      | ~ v1_partfun1(B_146,A_145)
      | v1_xboole_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_281,plain,(
    ! [C_147] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_147),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_147,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_147)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_278])).

tff(c_289,plain,(
    ! [C_147] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_147),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_147,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_147)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_138,c_138,c_281])).

tff(c_290,plain,(
    ! [C_147] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_147),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_147,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_289])).

tff(c_298,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1(k3_filter_1(A_149,B_150,C_151),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_149,B_150),k8_eqrel_1(A_149,B_150)),k8_eqrel_1(A_149,B_150))))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_149,A_149),A_149)))
      | ~ v1_funct_2(C_151,k2_zfmisc_1(A_149,A_149),A_149)
      | ~ v1_funct_1(C_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k2_zfmisc_1(A_149,A_149)))
      | ~ v8_relat_2(B_150)
      | ~ v3_relat_2(B_150)
      | ~ v1_partfun1(B_150,A_149)
      | v1_xboole_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_313,plain,(
    ! [C_151] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_151),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_151,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_151)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_298])).

tff(c_326,plain,(
    ! [C_151] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_151),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_151,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_151)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_138,c_138,c_313])).

tff(c_334,plain,(
    ! [C_152] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_152),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_152,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_326])).

tff(c_10,plain,(
    ! [A_11,B_12,C_14] :
      ( r3_binop_1(A_11,B_12,C_14)
      | ~ r2_binop_1(A_11,B_12,C_14)
      | ~ r1_binop_1(A_11,B_12,C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11,A_11),A_11)))
      | ~ v1_funct_2(C_14,k2_zfmisc_1(A_11,A_11),A_11)
      | ~ v1_funct_1(C_14)
      | ~ m1_subset_1(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_417,plain,(
    ! [B_171,C_172] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_171,k3_filter_1('#skF_1','#skF_2',C_172))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_171,k3_filter_1('#skF_1','#skF_2',C_172))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_171,k3_filter_1('#skF_1','#skF_2',C_172))
      | ~ v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_172),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_172))
      | ~ m1_subset_1(B_171,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_172,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_172) ) ),
    inference(resolution,[status(thm)],[c_334,c_10])).

tff(c_421,plain,(
    ! [B_173,C_174] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_174))
      | ~ m1_subset_1(B_173,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_174,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_174) ) ),
    inference(resolution,[status(thm)],[c_290,c_417])).

tff(c_423,plain,(
    ! [B_173] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_173,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_173,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_421])).

tff(c_449,plain,(
    ! [B_179] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_179,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_179,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_179,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_179,k7_eqrel_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_90,c_251,c_423])).

tff(c_42,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_140,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_42])).

tff(c_463,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_449,c_140])).

tff(c_464,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_467,plain,(
    ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_221,c_464])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_467])).

tff(c_472,plain,
    ( ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_474,plain,(
    ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_477,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_259,c_474])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_166,c_477])).

tff(c_482,plain,(
    ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_486,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_244,c_482])).

tff(c_490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_160,c_486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.60  
% 3.49/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.60  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.49/1.60  
% 3.49/1.60  %Foreground sorts:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Background operators:
% 3.49/1.60  
% 3.49/1.60  
% 3.49/1.60  %Foreground operators:
% 3.49/1.60  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.49/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.60  tff(m1_eqrel_1, type, m1_eqrel_1: ($i * $i) > $o).
% 3.49/1.60  tff(k7_eqrel_1, type, k7_eqrel_1: ($i * $i) > $i).
% 3.49/1.60  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.49/1.60  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 3.49/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.49/1.60  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 3.49/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.49/1.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.49/1.60  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 3.49/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.49/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.49/1.60  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.49/1.60  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.49/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.49/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.60  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 3.49/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.49/1.60  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 3.49/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.49/1.60  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.49/1.60  
% 3.49/1.63  tff(f_221, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_filter_1)).
% 3.49/1.63  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.49/1.63  tff(f_130, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.49/1.63  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_binop_1)).
% 3.49/1.63  tff(f_154, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k8_eqrel_1(A, B) = k7_eqrel_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_eqrel_1)).
% 3.49/1.63  tff(f_176, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_filter_1)).
% 3.49/1.63  tff(f_198, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_filter_1)).
% 3.49/1.63  tff(f_144, axiom, (![A, B]: (((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ~v1_xboole_0(k7_eqrel_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_eqrel_1)).
% 3.49/1.63  tff(f_97, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_eqrel_1(k8_eqrel_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_eqrel_1)).
% 3.49/1.63  tff(f_116, axiom, (![A, B]: (m1_eqrel_1(B, A) => m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_eqrel_1)).
% 3.49/1.63  tff(f_112, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.49/1.63  tff(f_49, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.49/1.63  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.49/1.63  tff(f_87, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.49/1.63  tff(c_48, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_46, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_58, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_70, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.49/1.63  tff(c_74, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_70])).
% 3.49/1.63  tff(c_75, plain, (![C_81, A_82, B_83]: (v1_funct_1(C_81) | ~m2_filter_1(C_81, A_82, B_83) | ~v1_relat_1(B_83) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.49/1.63  tff(c_78, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_75])).
% 3.49/1.63  tff(c_81, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_78])).
% 3.49/1.63  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_81])).
% 3.49/1.63  tff(c_84, plain, (![C_86, A_87, B_88]: (v1_funct_2(C_86, k2_zfmisc_1(A_87, A_87), A_87) | ~m2_filter_1(C_86, A_87, B_88) | ~v1_relat_1(B_88) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.49/1.63  tff(c_86, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_84])).
% 3.49/1.63  tff(c_89, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_86])).
% 3.49/1.63  tff(c_90, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_89])).
% 3.49/1.63  tff(c_102, plain, (![C_95, A_96, B_97]: (m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_96, A_96), A_96))) | ~m2_filter_1(C_95, A_96, B_97) | ~v1_relat_1(B_97) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.49/1.63  tff(c_104, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_102])).
% 3.49/1.63  tff(c_107, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_104])).
% 3.49/1.63  tff(c_108, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_107])).
% 3.49/1.63  tff(c_44, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_155, plain, (![A_107, B_108, C_109]: (r1_binop_1(A_107, B_108, C_109) | ~r3_binop_1(A_107, B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_107, A_107), A_107))) | ~v1_funct_2(C_109, k2_zfmisc_1(A_107, A_107), A_107) | ~v1_funct_1(C_109) | ~m1_subset_1(B_108, A_107))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.63  tff(c_157, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_155])).
% 3.49/1.63  tff(c_160, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_82, c_90, c_108, c_157])).
% 3.49/1.63  tff(c_56, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_54, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_52, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_132, plain, (![A_103, B_104]: (k8_eqrel_1(A_103, B_104)=k7_eqrel_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v1_partfun1(B_104, A_103) | ~v8_relat_2(B_104) | ~v3_relat_2(B_104))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.49/1.63  tff(c_135, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_132])).
% 3.49/1.63  tff(c_138, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_135])).
% 3.49/1.63  tff(c_238, plain, (![A_126, B_127, C_128, D_129]: (r1_binop_1(k8_eqrel_1(A_126, B_127), k9_eqrel_1(A_126, B_127, C_128), k3_filter_1(A_126, B_127, D_129)) | ~r1_binop_1(A_126, C_128, D_129) | ~m2_filter_1(D_129, A_126, B_127) | ~m1_subset_1(C_128, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(k2_zfmisc_1(A_126, A_126))) | ~v8_relat_2(B_127) | ~v3_relat_2(B_127) | ~v1_partfun1(B_127, A_126) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_176])).
% 3.49/1.63  tff(c_241, plain, (![C_128, D_129]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_128), k3_filter_1('#skF_1', '#skF_2', D_129)) | ~r1_binop_1('#skF_1', C_128, D_129) | ~m2_filter_1(D_129, '#skF_1', '#skF_2') | ~m1_subset_1(C_128, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_238])).
% 3.49/1.63  tff(c_243, plain, (![C_128, D_129]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_128), k3_filter_1('#skF_1', '#skF_2', D_129)) | ~r1_binop_1('#skF_1', C_128, D_129) | ~m2_filter_1(D_129, '#skF_1', '#skF_2') | ~m1_subset_1(C_128, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_241])).
% 3.49/1.63  tff(c_244, plain, (![C_128, D_129]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_128), k3_filter_1('#skF_1', '#skF_2', D_129)) | ~r1_binop_1('#skF_1', C_128, D_129) | ~m2_filter_1(D_129, '#skF_1', '#skF_2') | ~m1_subset_1(C_128, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_243])).
% 3.49/1.63  tff(c_161, plain, (![A_110, B_111, C_112]: (r2_binop_1(A_110, B_111, C_112) | ~r3_binop_1(A_110, B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_110, A_110), A_110))) | ~v1_funct_2(C_112, k2_zfmisc_1(A_110, A_110), A_110) | ~v1_funct_1(C_112) | ~m1_subset_1(B_111, A_110))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.63  tff(c_163, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_161])).
% 3.49/1.63  tff(c_166, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_82, c_90, c_108, c_163])).
% 3.49/1.63  tff(c_253, plain, (![A_133, B_134, C_135, D_136]: (r2_binop_1(k8_eqrel_1(A_133, B_134), k9_eqrel_1(A_133, B_134, C_135), k3_filter_1(A_133, B_134, D_136)) | ~r2_binop_1(A_133, C_135, D_136) | ~m2_filter_1(D_136, A_133, B_134) | ~m1_subset_1(C_135, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(k2_zfmisc_1(A_133, A_133))) | ~v8_relat_2(B_134) | ~v3_relat_2(B_134) | ~v1_partfun1(B_134, A_133) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_198])).
% 3.49/1.63  tff(c_256, plain, (![C_135, D_136]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_135), k3_filter_1('#skF_1', '#skF_2', D_136)) | ~r2_binop_1('#skF_1', C_135, D_136) | ~m2_filter_1(D_136, '#skF_1', '#skF_2') | ~m1_subset_1(C_135, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_253])).
% 3.49/1.63  tff(c_258, plain, (![C_135, D_136]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_135), k3_filter_1('#skF_1', '#skF_2', D_136)) | ~r2_binop_1('#skF_1', C_135, D_136) | ~m2_filter_1(D_136, '#skF_1', '#skF_2') | ~m1_subset_1(C_135, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_256])).
% 3.49/1.63  tff(c_259, plain, (![C_135, D_136]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_135), k3_filter_1('#skF_1', '#skF_2', D_136)) | ~r2_binop_1('#skF_1', C_135, D_136) | ~m2_filter_1(D_136, '#skF_1', '#skF_2') | ~m1_subset_1(C_135, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_258])).
% 3.49/1.63  tff(c_145, plain, (![A_105, B_106]: (~v1_xboole_0(k7_eqrel_1(A_105, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_zfmisc_1(A_105, A_105))) | ~v1_partfun1(B_106, A_105) | ~v8_relat_2(B_106) | ~v3_relat_2(B_106) | v1_xboole_0(A_105))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.49/1.63  tff(c_148, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_145])).
% 3.49/1.63  tff(c_151, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_148])).
% 3.49/1.63  tff(c_152, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_151])).
% 3.49/1.63  tff(c_109, plain, (![A_98, B_99]: (m1_eqrel_1(k8_eqrel_1(A_98, B_99), A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v1_partfun1(B_99, A_98) | ~v8_relat_2(B_99) | ~v3_relat_2(B_99))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.49/1.63  tff(c_112, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_109])).
% 3.49/1.63  tff(c_115, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_112])).
% 3.49/1.63  tff(c_139, plain, (m1_eqrel_1(k7_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_115])).
% 3.49/1.63  tff(c_26, plain, (![B_24, A_23]: (m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))) | ~m1_eqrel_1(B_24, A_23))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.49/1.63  tff(c_167, plain, (![A_113, B_114, C_115]: (m2_subset_1(k9_eqrel_1(A_113, B_114, C_115), k1_zfmisc_1(A_113), k8_eqrel_1(A_113, B_114)) | ~m1_subset_1(C_115, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_zfmisc_1(A_113, A_113))) | ~v1_partfun1(B_114, A_113) | ~v8_relat_2(B_114) | ~v3_relat_2(B_114) | v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.49/1.63  tff(c_172, plain, (![C_115]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_115), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_115, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_167])).
% 3.49/1.63  tff(c_175, plain, (![C_115]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_115), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_115, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_50, c_172])).
% 3.49/1.63  tff(c_183, plain, (![C_119]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_119), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_175])).
% 3.49/1.63  tff(c_6, plain, (![C_10, B_8, A_7]: (m1_subset_1(C_10, B_8) | ~m2_subset_1(C_10, A_7, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)) | v1_xboole_0(B_8) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.49/1.63  tff(c_185, plain, (![C_119]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_119), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_119, '#skF_1'))), inference(resolution, [status(thm)], [c_183, c_6])).
% 3.49/1.63  tff(c_188, plain, (![C_119]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_119), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_152, c_185])).
% 3.49/1.63  tff(c_200, plain, (~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_188])).
% 3.49/1.63  tff(c_203, plain, (~m1_eqrel_1(k7_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_26, c_200])).
% 3.49/1.63  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_203])).
% 3.49/1.63  tff(c_209, plain, (m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_188])).
% 3.49/1.63  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.49/1.63  tff(c_214, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_209, c_2])).
% 3.49/1.63  tff(c_220, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_152, c_214])).
% 3.49/1.63  tff(c_208, plain, (![C_119]: (v1_xboole_0(k1_zfmisc_1('#skF_1')) | m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_119), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_119, '#skF_1'))), inference(splitRight, [status(thm)], [c_188])).
% 3.49/1.63  tff(c_221, plain, (![C_119]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_119), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_119, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_220, c_208])).
% 3.49/1.63  tff(c_231, plain, (![A_123, B_124, C_125]: (v1_funct_1(k3_filter_1(A_123, B_124, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_123, A_123), A_123))) | ~v1_funct_2(C_125, k2_zfmisc_1(A_123, A_123), A_123) | ~v1_funct_1(C_125) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1(A_123, A_123))) | ~v8_relat_2(B_124) | ~v3_relat_2(B_124) | ~v1_partfun1(B_124, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.63  tff(c_233, plain, (![B_124]: (v1_funct_1(k3_filter_1('#skF_1', B_124, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_124) | ~v3_relat_2(B_124) | ~v1_partfun1(B_124, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_108, c_231])).
% 3.49/1.63  tff(c_236, plain, (![B_124]: (v1_funct_1(k3_filter_1('#skF_1', B_124, '#skF_4')) | ~m1_subset_1(B_124, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_124) | ~v3_relat_2(B_124) | ~v1_partfun1(B_124, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_90, c_233])).
% 3.49/1.63  tff(c_245, plain, (![B_130]: (v1_funct_1(k3_filter_1('#skF_1', B_130, '#skF_4')) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_130) | ~v3_relat_2(B_130) | ~v1_partfun1(B_130, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_236])).
% 3.49/1.63  tff(c_248, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_245])).
% 3.49/1.63  tff(c_251, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_248])).
% 3.49/1.63  tff(c_278, plain, (![A_145, B_146, C_147]: (v1_funct_2(k3_filter_1(A_145, B_146, C_147), k2_zfmisc_1(k8_eqrel_1(A_145, B_146), k8_eqrel_1(A_145, B_146)), k8_eqrel_1(A_145, B_146)) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_145, A_145), A_145))) | ~v1_funct_2(C_147, k2_zfmisc_1(A_145, A_145), A_145) | ~v1_funct_1(C_147) | ~m1_subset_1(B_146, k1_zfmisc_1(k2_zfmisc_1(A_145, A_145))) | ~v8_relat_2(B_146) | ~v3_relat_2(B_146) | ~v1_partfun1(B_146, A_145) | v1_xboole_0(A_145))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.63  tff(c_281, plain, (![C_147]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_147), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_147, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_147) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_278])).
% 3.49/1.63  tff(c_289, plain, (![C_147]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_147), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_147, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_147) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_138, c_138, c_281])).
% 3.49/1.63  tff(c_290, plain, (![C_147]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_147), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_147, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_147))), inference(negUnitSimplification, [status(thm)], [c_58, c_289])).
% 3.49/1.63  tff(c_298, plain, (![A_149, B_150, C_151]: (m1_subset_1(k3_filter_1(A_149, B_150, C_151), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_149, B_150), k8_eqrel_1(A_149, B_150)), k8_eqrel_1(A_149, B_150)))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_149, A_149), A_149))) | ~v1_funct_2(C_151, k2_zfmisc_1(A_149, A_149), A_149) | ~v1_funct_1(C_151) | ~m1_subset_1(B_150, k1_zfmisc_1(k2_zfmisc_1(A_149, A_149))) | ~v8_relat_2(B_150) | ~v3_relat_2(B_150) | ~v1_partfun1(B_150, A_149) | v1_xboole_0(A_149))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.49/1.63  tff(c_313, plain, (![C_151]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_151), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_151, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_151) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_298])).
% 3.49/1.63  tff(c_326, plain, (![C_151]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_151), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_151, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_151) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_138, c_138, c_313])).
% 3.49/1.63  tff(c_334, plain, (![C_152]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_152), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_152, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_152))), inference(negUnitSimplification, [status(thm)], [c_58, c_326])).
% 3.49/1.63  tff(c_10, plain, (![A_11, B_12, C_14]: (r3_binop_1(A_11, B_12, C_14) | ~r2_binop_1(A_11, B_12, C_14) | ~r1_binop_1(A_11, B_12, C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11, A_11), A_11))) | ~v1_funct_2(C_14, k2_zfmisc_1(A_11, A_11), A_11) | ~v1_funct_1(C_14) | ~m1_subset_1(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.63  tff(c_417, plain, (![B_171, C_172]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_171, k3_filter_1('#skF_1', '#skF_2', C_172)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_171, k3_filter_1('#skF_1', '#skF_2', C_172)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_171, k3_filter_1('#skF_1', '#skF_2', C_172)) | ~v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_172), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_172)) | ~m1_subset_1(B_171, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_172, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_172))), inference(resolution, [status(thm)], [c_334, c_10])).
% 3.49/1.63  tff(c_421, plain, (![B_173, C_174]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', C_174)) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_174)) | ~m1_subset_1(B_173, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_174, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_174))), inference(resolution, [status(thm)], [c_290, c_417])).
% 3.49/1.63  tff(c_423, plain, (![B_173]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_173, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_173, k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_421])).
% 3.49/1.63  tff(c_449, plain, (![B_179]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_179, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_179, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_179, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_179, k7_eqrel_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_90, c_251, c_423])).
% 3.49/1.63  tff(c_42, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.49/1.63  tff(c_140, plain, (~r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_42])).
% 3.49/1.63  tff(c_463, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_449, c_140])).
% 3.49/1.63  tff(c_464, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_463])).
% 3.49/1.63  tff(c_467, plain, (~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_221, c_464])).
% 3.49/1.63  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_467])).
% 3.49/1.63  tff(c_472, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_463])).
% 3.49/1.63  tff(c_474, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_472])).
% 3.49/1.63  tff(c_477, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_259, c_474])).
% 3.49/1.63  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_166, c_477])).
% 3.49/1.63  tff(c_482, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_472])).
% 3.49/1.63  tff(c_486, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_244, c_482])).
% 3.49/1.63  tff(c_490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_160, c_486])).
% 3.49/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.63  
% 3.49/1.63  Inference rules
% 3.49/1.63  ----------------------
% 3.49/1.63  #Ref     : 0
% 3.49/1.63  #Sup     : 75
% 3.49/1.63  #Fact    : 0
% 3.49/1.63  #Define  : 0
% 3.49/1.63  #Split   : 8
% 3.49/1.63  #Chain   : 0
% 3.49/1.63  #Close   : 0
% 3.49/1.63  
% 3.49/1.63  Ordering : KBO
% 3.49/1.63  
% 3.49/1.63  Simplification rules
% 3.49/1.63  ----------------------
% 3.49/1.63  #Subsume      : 15
% 3.49/1.63  #Demod        : 164
% 3.49/1.63  #Tautology    : 11
% 3.49/1.63  #SimpNegUnit  : 35
% 3.49/1.63  #BackRed      : 2
% 3.49/1.63  
% 3.49/1.63  #Partial instantiations: 0
% 3.49/1.63  #Strategies tried      : 1
% 3.49/1.63  
% 3.49/1.63  Timing (in seconds)
% 3.49/1.63  ----------------------
% 3.49/1.63  Preprocessing        : 0.39
% 3.49/1.63  Parsing              : 0.20
% 3.49/1.63  CNF conversion       : 0.03
% 3.49/1.63  Main loop            : 0.44
% 3.49/1.63  Inferencing          : 0.16
% 3.49/1.63  Reduction            : 0.14
% 3.49/1.63  Demodulation         : 0.10
% 3.49/1.63  BG Simplification    : 0.03
% 3.49/1.63  Subsumption          : 0.09
% 3.49/1.63  Abstraction          : 0.02
% 3.49/1.63  MUC search           : 0.00
% 3.49/1.64  Cooper               : 0.00
% 3.49/1.64  Total                : 0.89
% 3.49/1.64  Index Insertion      : 0.00
% 3.49/1.64  Index Deletion       : 0.00
% 3.49/1.64  Index Matching       : 0.00
% 3.49/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
