%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  140 (1139 expanded)
%              Number of leaves         :   42 ( 441 expanded)
%              Depth                    :   16
%              Number of atoms          :  438 (4791 expanded)
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

tff(f_226,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_filter_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
         => ( r3_binop_1(A,B,C)
          <=> ( r1_binop_1(A,B,C)
              & r2_binop_1(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_binop_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_181,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_filter_1)).

tff(f_203,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_filter_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ~ v1_xboole_0(k7_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_eqrel_1)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( m1_eqrel_1(B,A)
     => m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_filter_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_48,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_63,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_73,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_84,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_funct_1(C_84)
      | ~ m2_filter_1(C_84,A_85,B_86)
      | ~ v1_relat_1(B_86)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_87,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_84])).

tff(c_90,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_87])).

tff(c_91,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_90])).

tff(c_93,plain,(
    ! [C_89,A_90,B_91] :
      ( v1_funct_2(C_89,k2_zfmisc_1(A_90,A_90),A_90)
      | ~ m2_filter_1(C_89,A_90,B_91)
      | ~ v1_relat_1(B_91)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_95,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_93])).

tff(c_98,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_95])).

tff(c_99,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_98])).

tff(c_112,plain,(
    ! [C_100,A_101,B_102] :
      ( m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_101,A_101),A_101)))
      | ~ m2_filter_1(C_100,A_101,B_102)
      | ~ v1_relat_1(B_102)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_114,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_117,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_114])).

tff(c_118,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_117])).

tff(c_46,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_173,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_binop_1(A_115,B_116,C_117)
      | ~ r3_binop_1(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_115,A_115),A_115)))
      | ~ v1_funct_2(C_117,k2_zfmisc_1(A_115,A_115),A_115)
      | ~ v1_funct_1(C_117)
      | ~ m1_subset_1(B_116,A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_175,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_173])).

tff(c_178,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91,c_99,c_118,c_175])).

tff(c_58,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_56,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_54,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_152,plain,(
    ! [A_110,B_111] :
      ( k8_eqrel_1(A_110,B_111) = k7_eqrel_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_zfmisc_1(A_110,A_110)))
      | ~ v1_partfun1(B_111,A_110)
      | ~ v8_relat_2(B_111)
      | ~ v3_relat_2(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_155,plain,
    ( k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_152])).

tff(c_158,plain,(
    k8_eqrel_1('#skF_1','#skF_2') = k7_eqrel_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_58,c_155])).

tff(c_270,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( r1_binop_1(k8_eqrel_1(A_138,B_139),k9_eqrel_1(A_138,B_139,C_140),k3_filter_1(A_138,B_139,D_141))
      | ~ r1_binop_1(A_138,C_140,D_141)
      | ~ m2_filter_1(D_141,A_138,B_139)
      | ~ m1_subset_1(C_140,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_zfmisc_1(A_138,A_138)))
      | ~ v8_relat_2(B_139)
      | ~ v3_relat_2(B_139)
      | ~ v1_partfun1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_273,plain,(
    ! [C_140,D_141] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_140),k3_filter_1('#skF_1','#skF_2',D_141))
      | ~ r1_binop_1('#skF_1',C_140,D_141)
      | ~ m2_filter_1(D_141,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_140,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_270])).

tff(c_275,plain,(
    ! [C_140,D_141] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_140),k3_filter_1('#skF_1','#skF_2',D_141))
      | ~ r1_binop_1('#skF_1',C_140,D_141)
      | ~ m2_filter_1(D_141,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_140,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_273])).

tff(c_276,plain,(
    ! [C_140,D_141] :
      ( r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_140),k3_filter_1('#skF_1','#skF_2',D_141))
      | ~ r1_binop_1('#skF_1',C_140,D_141)
      | ~ m2_filter_1(D_141,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_140,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_167,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_binop_1(A_112,B_113,C_114)
      | ~ r3_binop_1(A_112,B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_112,A_112),A_112)))
      | ~ v1_funct_2(C_114,k2_zfmisc_1(A_112,A_112),A_112)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(B_113,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_169,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_172,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_91,c_99,c_118,c_169])).

tff(c_262,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( r2_binop_1(k8_eqrel_1(A_132,B_133),k9_eqrel_1(A_132,B_133,C_134),k3_filter_1(A_132,B_133,D_135))
      | ~ r2_binop_1(A_132,C_134,D_135)
      | ~ m2_filter_1(D_135,A_132,B_133)
      | ~ m1_subset_1(C_134,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(A_132,A_132)))
      | ~ v8_relat_2(B_133)
      | ~ v3_relat_2(B_133)
      | ~ v1_partfun1(B_133,A_132)
      | v1_xboole_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_265,plain,(
    ! [C_134,D_135] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_134),k3_filter_1('#skF_1','#skF_2',D_135))
      | ~ r2_binop_1('#skF_1',C_134,D_135)
      | ~ m2_filter_1(D_135,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_134,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_262])).

tff(c_267,plain,(
    ! [C_134,D_135] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_134),k3_filter_1('#skF_1','#skF_2',D_135))
      | ~ r2_binop_1('#skF_1',C_134,D_135)
      | ~ m2_filter_1(D_135,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_134,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_265])).

tff(c_268,plain,(
    ! [C_134,D_135] :
      ( r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2',C_134),k3_filter_1('#skF_1','#skF_2',D_135))
      | ~ r2_binop_1('#skF_1',C_134,D_135)
      | ~ m2_filter_1(D_135,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_134,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_267])).

tff(c_144,plain,(
    ! [A_108,B_109] :
      ( ~ v1_xboole_0(k7_eqrel_1(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k2_zfmisc_1(A_108,A_108)))
      | ~ v1_partfun1(B_109,A_108)
      | ~ v8_relat_2(B_109)
      | ~ v3_relat_2(B_109)
      | v1_xboole_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_147,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_144])).

tff(c_150,plain,
    ( ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_58,c_147])).

tff(c_151,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_150])).

tff(c_137,plain,(
    ! [A_106,B_107] :
      ( m1_eqrel_1(k8_eqrel_1(A_106,B_107),A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v1_partfun1(B_107,A_106)
      | ~ v8_relat_2(B_107)
      | ~ v3_relat_2(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_140,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_137])).

tff(c_143,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_58,c_140])).

tff(c_159,plain,(
    m1_eqrel_1(k7_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_143])).

tff(c_28,plain,(
    ! [B_26,A_25] :
      ( m1_subset_1(B_26,k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ m1_eqrel_1(B_26,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_179,plain,(
    ! [A_118,B_119,C_120] :
      ( m2_subset_1(k9_eqrel_1(A_118,B_119,C_120),k1_zfmisc_1(A_118),k8_eqrel_1(A_118,B_119))
      | ~ m1_subset_1(C_120,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_zfmisc_1(A_118,A_118)))
      | ~ v1_partfun1(B_119,A_118)
      | ~ v8_relat_2(B_119)
      | ~ v3_relat_2(B_119)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_184,plain,(
    ! [C_120] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_120),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_120,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v1_partfun1('#skF_2','#skF_1')
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_179])).

tff(c_187,plain,(
    ! [C_120] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_120),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_120,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_58,c_52,c_184])).

tff(c_189,plain,(
    ! [C_121] :
      ( m2_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_121),k1_zfmisc_1('#skF_1'),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_121,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_187])).

tff(c_8,plain,(
    ! [C_12,B_10,A_9] :
      ( m1_subset_1(C_12,B_10)
      | ~ m2_subset_1(C_12,A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9))
      | v1_xboole_0(B_10)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_191,plain,(
    ! [C_121] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_121),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_121,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_189,c_8])).

tff(c_194,plain,(
    ! [C_121] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_121),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
      | v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_121,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_191])).

tff(c_195,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_198,plain,(
    ~ m1_eqrel_1(k7_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_198])).

tff(c_204,plain,(
    m1_subset_1(k7_eqrel_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_xboole_0(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_209,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_1','#skF_2'))
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_218,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_209])).

tff(c_203,plain,(
    ! [C_121] :
      ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
      | m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_121),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_121,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_221,plain,(
    ! [C_121] :
      ( m1_subset_1(k9_eqrel_1('#skF_1','#skF_2',C_121),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_121,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_203])).

tff(c_248,plain,(
    ! [A_128,B_129,C_130] :
      ( v1_funct_1(k3_filter_1(A_128,B_129,C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_128,A_128),A_128)))
      | ~ v1_funct_2(C_130,k2_zfmisc_1(A_128,A_128),A_128)
      | ~ v1_funct_1(C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129)
      | ~ v1_partfun1(B_129,A_128)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_250,plain,(
    ! [B_129] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_129,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129)
      | ~ v1_partfun1(B_129,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_118,c_248])).

tff(c_253,plain,(
    ! [B_129] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_129,'#skF_4'))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129)
      | ~ v1_partfun1(B_129,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_99,c_250])).

tff(c_255,plain,(
    ! [B_131] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_131,'#skF_4'))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_131)
      | ~ v3_relat_2(B_131)
      | ~ v1_partfun1(B_131,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_253])).

tff(c_258,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_255])).

tff(c_261,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_258])).

tff(c_278,plain,(
    ! [A_144,B_145,C_146] :
      ( v1_funct_2(k3_filter_1(A_144,B_145,C_146),k2_zfmisc_1(k8_eqrel_1(A_144,B_145),k8_eqrel_1(A_144,B_145)),k8_eqrel_1(A_144,B_145))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_144,A_144),A_144)))
      | ~ v1_funct_2(C_146,k2_zfmisc_1(A_144,A_144),A_144)
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(k2_zfmisc_1(A_144,A_144)))
      | ~ v8_relat_2(B_145)
      | ~ v3_relat_2(B_145)
      | ~ v1_partfun1(B_145,A_144)
      | v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_281,plain,(
    ! [C_146] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_146),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_146,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_146)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_278])).

tff(c_289,plain,(
    ! [C_146] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_146),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_146,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_146)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_158,c_158,c_281])).

tff(c_290,plain,(
    ! [C_146] :
      ( v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_146),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_146,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_289])).

tff(c_298,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k3_filter_1(A_148,B_149,C_150),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_148,B_149),k8_eqrel_1(A_148,B_149)),k8_eqrel_1(A_148,B_149))))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_148,A_148),A_148)))
      | ~ v1_funct_2(C_150,k2_zfmisc_1(A_148,A_148),A_148)
      | ~ v1_funct_1(C_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1(A_148,A_148)))
      | ~ v8_relat_2(B_149)
      | ~ v3_relat_2(B_149)
      | ~ v1_partfun1(B_149,A_148)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_313,plain,(
    ! [C_150] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_150),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k8_eqrel_1('#skF_1','#skF_2')),k8_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_150,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_150)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2('#skF_2')
      | ~ v3_relat_2('#skF_2')
      | ~ v1_partfun1('#skF_2','#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_298])).

tff(c_328,plain,(
    ! [C_150] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_150),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_150,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_150)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_158,c_158,c_313])).

tff(c_336,plain,(
    ! [C_151] :
      ( m1_subset_1(k3_filter_1('#skF_1','#skF_2',C_151),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_151,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_328])).

tff(c_12,plain,(
    ! [A_13,B_14,C_16] :
      ( r3_binop_1(A_13,B_14,C_16)
      | ~ r2_binop_1(A_13,B_14,C_16)
      | ~ r1_binop_1(A_13,B_14,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13,A_13),A_13)))
      | ~ v1_funct_2(C_16,k2_zfmisc_1(A_13,A_13),A_13)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_460,plain,(
    ! [B_180,C_181] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_180,k3_filter_1('#skF_1','#skF_2',C_181))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_180,k3_filter_1('#skF_1','#skF_2',C_181))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_180,k3_filter_1('#skF_1','#skF_2',C_181))
      | ~ v1_funct_2(k3_filter_1('#skF_1','#skF_2',C_181),k2_zfmisc_1(k7_eqrel_1('#skF_1','#skF_2'),k7_eqrel_1('#skF_1','#skF_2')),k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_181))
      | ~ m1_subset_1(B_180,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_181,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_336,c_12])).

tff(c_464,plain,(
    ! [B_182,C_183] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2',C_183))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2',C_183))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2',C_183))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2',C_183))
      | ~ m1_subset_1(B_182,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
      | ~ v1_funct_2(C_183,k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_290,c_460])).

tff(c_466,plain,(
    ! [B_182] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_182,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_182,k7_eqrel_1('#skF_1','#skF_2'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_118,c_464])).

tff(c_470,plain,(
    ! [B_184] :
      ( r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_184,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_184,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),B_184,k3_filter_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_subset_1(B_184,k7_eqrel_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_99,c_261,c_466])).

tff(c_44,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_160,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_44])).

tff(c_484,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_470,c_160])).

tff(c_485,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k7_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_488,plain,(
    ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_221,c_485])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_488])).

tff(c_493,plain,
    ( ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_495,plain,(
    ~ r2_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_517,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_268,c_495])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_172,c_517])).

tff(c_522,plain,(
    ~ r1_binop_1(k7_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_526,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_276,c_522])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_178,c_526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:02:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  
% 3.50/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.60  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.50/1.60  
% 3.50/1.60  %Foreground sorts:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Background operators:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Foreground operators:
% 3.50/1.60  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.50/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.60  tff(m1_eqrel_1, type, m1_eqrel_1: ($i * $i) > $o).
% 3.50/1.60  tff(k7_eqrel_1, type, k7_eqrel_1: ($i * $i) > $i).
% 3.50/1.60  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.50/1.60  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 3.50/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.50/1.60  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 3.50/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.50/1.60  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 3.50/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.60  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.60  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.50/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.60  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 3.50/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.60  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 3.50/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.60  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.50/1.60  
% 3.88/1.63  tff(f_226, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_filter_1)).
% 3.88/1.63  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.88/1.63  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.88/1.63  tff(f_135, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.88/1.63  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_binop_1)).
% 3.88/1.64  tff(f_159, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k8_eqrel_1(A, B) = k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_eqrel_1)).
% 3.88/1.64  tff(f_181, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_filter_1)).
% 3.88/1.64  tff(f_203, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_filter_1)).
% 3.88/1.64  tff(f_149, axiom, (![A, B]: (((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ~v1_xboole_0(k7_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_eqrel_1)).
% 3.88/1.64  tff(f_102, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_eqrel_1(k8_eqrel_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_eqrel_1)).
% 3.88/1.64  tff(f_121, axiom, (![A, B]: (m1_eqrel_1(B, A) => m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_eqrel_1)).
% 3.88/1.64  tff(f_117, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.88/1.64  tff(f_54, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.88/1.64  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.88/1.64  tff(f_92, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.88/1.64  tff(c_50, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_48, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_60, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.88/1.64  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_63, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.88/1.64  tff(c_69, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_63])).
% 3.88/1.64  tff(c_73, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_69])).
% 3.88/1.64  tff(c_84, plain, (![C_84, A_85, B_86]: (v1_funct_1(C_84) | ~m2_filter_1(C_84, A_85, B_86) | ~v1_relat_1(B_86) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.88/1.64  tff(c_87, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_84])).
% 3.88/1.64  tff(c_90, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_87])).
% 3.88/1.64  tff(c_91, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_90])).
% 3.88/1.64  tff(c_93, plain, (![C_89, A_90, B_91]: (v1_funct_2(C_89, k2_zfmisc_1(A_90, A_90), A_90) | ~m2_filter_1(C_89, A_90, B_91) | ~v1_relat_1(B_91) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.88/1.64  tff(c_95, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_93])).
% 3.88/1.64  tff(c_98, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_95])).
% 3.88/1.64  tff(c_99, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_98])).
% 3.88/1.64  tff(c_112, plain, (![C_100, A_101, B_102]: (m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_101, A_101), A_101))) | ~m2_filter_1(C_100, A_101, B_102) | ~v1_relat_1(B_102) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.88/1.64  tff(c_114, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_112])).
% 3.88/1.64  tff(c_117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_114])).
% 3.88/1.64  tff(c_118, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_60, c_117])).
% 3.88/1.64  tff(c_46, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_173, plain, (![A_115, B_116, C_117]: (r1_binop_1(A_115, B_116, C_117) | ~r3_binop_1(A_115, B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_115, A_115), A_115))) | ~v1_funct_2(C_117, k2_zfmisc_1(A_115, A_115), A_115) | ~v1_funct_1(C_117) | ~m1_subset_1(B_116, A_115))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.88/1.64  tff(c_175, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_173])).
% 3.88/1.64  tff(c_178, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91, c_99, c_118, c_175])).
% 3.88/1.64  tff(c_58, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_56, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_54, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_152, plain, (![A_110, B_111]: (k8_eqrel_1(A_110, B_111)=k7_eqrel_1(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(k2_zfmisc_1(A_110, A_110))) | ~v1_partfun1(B_111, A_110) | ~v8_relat_2(B_111) | ~v3_relat_2(B_111))), inference(cnfTransformation, [status(thm)], [f_159])).
% 3.88/1.64  tff(c_155, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_52, c_152])).
% 3.88/1.64  tff(c_158, plain, (k8_eqrel_1('#skF_1', '#skF_2')=k7_eqrel_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_58, c_155])).
% 3.88/1.64  tff(c_270, plain, (![A_138, B_139, C_140, D_141]: (r1_binop_1(k8_eqrel_1(A_138, B_139), k9_eqrel_1(A_138, B_139, C_140), k3_filter_1(A_138, B_139, D_141)) | ~r1_binop_1(A_138, C_140, D_141) | ~m2_filter_1(D_141, A_138, B_139) | ~m1_subset_1(C_140, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(k2_zfmisc_1(A_138, A_138))) | ~v8_relat_2(B_139) | ~v3_relat_2(B_139) | ~v1_partfun1(B_139, A_138) | v1_xboole_0(A_138))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.88/1.64  tff(c_273, plain, (![C_140, D_141]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_140), k3_filter_1('#skF_1', '#skF_2', D_141)) | ~r1_binop_1('#skF_1', C_140, D_141) | ~m2_filter_1(D_141, '#skF_1', '#skF_2') | ~m1_subset_1(C_140, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_270])).
% 3.88/1.64  tff(c_275, plain, (![C_140, D_141]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_140), k3_filter_1('#skF_1', '#skF_2', D_141)) | ~r1_binop_1('#skF_1', C_140, D_141) | ~m2_filter_1(D_141, '#skF_1', '#skF_2') | ~m1_subset_1(C_140, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_273])).
% 3.88/1.64  tff(c_276, plain, (![C_140, D_141]: (r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_140), k3_filter_1('#skF_1', '#skF_2', D_141)) | ~r1_binop_1('#skF_1', C_140, D_141) | ~m2_filter_1(D_141, '#skF_1', '#skF_2') | ~m1_subset_1(C_140, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 3.88/1.64  tff(c_167, plain, (![A_112, B_113, C_114]: (r2_binop_1(A_112, B_113, C_114) | ~r3_binop_1(A_112, B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_112, A_112), A_112))) | ~v1_funct_2(C_114, k2_zfmisc_1(A_112, A_112), A_112) | ~v1_funct_1(C_114) | ~m1_subset_1(B_113, A_112))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.88/1.64  tff(c_169, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_167])).
% 3.88/1.64  tff(c_172, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_91, c_99, c_118, c_169])).
% 3.88/1.64  tff(c_262, plain, (![A_132, B_133, C_134, D_135]: (r2_binop_1(k8_eqrel_1(A_132, B_133), k9_eqrel_1(A_132, B_133, C_134), k3_filter_1(A_132, B_133, D_135)) | ~r2_binop_1(A_132, C_134, D_135) | ~m2_filter_1(D_135, A_132, B_133) | ~m1_subset_1(C_134, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(A_132, A_132))) | ~v8_relat_2(B_133) | ~v3_relat_2(B_133) | ~v1_partfun1(B_133, A_132) | v1_xboole_0(A_132))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.88/1.64  tff(c_265, plain, (![C_134, D_135]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_134), k3_filter_1('#skF_1', '#skF_2', D_135)) | ~r2_binop_1('#skF_1', C_134, D_135) | ~m2_filter_1(D_135, '#skF_1', '#skF_2') | ~m1_subset_1(C_134, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_262])).
% 3.88/1.64  tff(c_267, plain, (![C_134, D_135]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_134), k3_filter_1('#skF_1', '#skF_2', D_135)) | ~r2_binop_1('#skF_1', C_134, D_135) | ~m2_filter_1(D_135, '#skF_1', '#skF_2') | ~m1_subset_1(C_134, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_265])).
% 3.88/1.64  tff(c_268, plain, (![C_134, D_135]: (r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', C_134), k3_filter_1('#skF_1', '#skF_2', D_135)) | ~r2_binop_1('#skF_1', C_134, D_135) | ~m2_filter_1(D_135, '#skF_1', '#skF_2') | ~m1_subset_1(C_134, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_267])).
% 3.88/1.64  tff(c_144, plain, (![A_108, B_109]: (~v1_xboole_0(k7_eqrel_1(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(k2_zfmisc_1(A_108, A_108))) | ~v1_partfun1(B_109, A_108) | ~v8_relat_2(B_109) | ~v3_relat_2(B_109) | v1_xboole_0(A_108))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.88/1.64  tff(c_147, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_144])).
% 3.88/1.64  tff(c_150, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_58, c_147])).
% 3.88/1.64  tff(c_151, plain, (~v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_150])).
% 3.88/1.64  tff(c_137, plain, (![A_106, B_107]: (m1_eqrel_1(k8_eqrel_1(A_106, B_107), A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v1_partfun1(B_107, A_106) | ~v8_relat_2(B_107) | ~v3_relat_2(B_107))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.88/1.64  tff(c_140, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_52, c_137])).
% 3.88/1.64  tff(c_143, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_58, c_140])).
% 3.88/1.64  tff(c_159, plain, (m1_eqrel_1(k7_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_143])).
% 3.88/1.64  tff(c_28, plain, (![B_26, A_25]: (m1_subset_1(B_26, k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~m1_eqrel_1(B_26, A_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.88/1.64  tff(c_179, plain, (![A_118, B_119, C_120]: (m2_subset_1(k9_eqrel_1(A_118, B_119, C_120), k1_zfmisc_1(A_118), k8_eqrel_1(A_118, B_119)) | ~m1_subset_1(C_120, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(k2_zfmisc_1(A_118, A_118))) | ~v1_partfun1(B_119, A_118) | ~v8_relat_2(B_119) | ~v3_relat_2(B_119) | v1_xboole_0(A_118))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.88/1.64  tff(c_184, plain, (![C_120]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_120), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_120, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_179])).
% 3.88/1.64  tff(c_187, plain, (![C_120]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_120), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_120, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_58, c_52, c_184])).
% 3.88/1.64  tff(c_189, plain, (![C_121]: (m2_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_121), k1_zfmisc_1('#skF_1'), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_121, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_187])).
% 3.88/1.64  tff(c_8, plain, (![C_12, B_10, A_9]: (m1_subset_1(C_12, B_10) | ~m2_subset_1(C_12, A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)) | v1_xboole_0(B_10) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.88/1.64  tff(c_191, plain, (![C_121]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_121), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_121, '#skF_1'))), inference(resolution, [status(thm)], [c_189, c_8])).
% 3.88/1.64  tff(c_194, plain, (![C_121]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_121), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_121, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_151, c_191])).
% 3.88/1.64  tff(c_195, plain, (~m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_194])).
% 3.88/1.64  tff(c_198, plain, (~m1_eqrel_1(k7_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_28, c_195])).
% 3.88/1.64  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_198])).
% 3.88/1.64  tff(c_204, plain, (m1_subset_1(k7_eqrel_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_194])).
% 3.88/1.64  tff(c_2, plain, (![B_3, A_1]: (v1_xboole_0(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.88/1.64  tff(c_209, plain, (v1_xboole_0(k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_204, c_2])).
% 3.88/1.64  tff(c_218, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_151, c_209])).
% 3.88/1.64  tff(c_203, plain, (![C_121]: (v1_xboole_0(k1_zfmisc_1('#skF_1')) | m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_121), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_121, '#skF_1'))), inference(splitRight, [status(thm)], [c_194])).
% 3.88/1.64  tff(c_221, plain, (![C_121]: (m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', C_121), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_121, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_218, c_203])).
% 3.88/1.64  tff(c_248, plain, (![A_128, B_129, C_130]: (v1_funct_1(k3_filter_1(A_128, B_129, C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_128, A_128), A_128))) | ~v1_funct_2(C_130, k2_zfmisc_1(A_128, A_128), A_128) | ~v1_funct_1(C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(A_128, A_128))) | ~v8_relat_2(B_129) | ~v3_relat_2(B_129) | ~v1_partfun1(B_129, A_128) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.64  tff(c_250, plain, (![B_129]: (v1_funct_1(k3_filter_1('#skF_1', B_129, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_129) | ~v3_relat_2(B_129) | ~v1_partfun1(B_129, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_118, c_248])).
% 3.88/1.64  tff(c_253, plain, (![B_129]: (v1_funct_1(k3_filter_1('#skF_1', B_129, '#skF_4')) | ~m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_129) | ~v3_relat_2(B_129) | ~v1_partfun1(B_129, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_99, c_250])).
% 3.88/1.64  tff(c_255, plain, (![B_131]: (v1_funct_1(k3_filter_1('#skF_1', B_131, '#skF_4')) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_131) | ~v3_relat_2(B_131) | ~v1_partfun1(B_131, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_60, c_253])).
% 3.88/1.64  tff(c_258, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_255])).
% 3.88/1.64  tff(c_261, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_258])).
% 3.88/1.64  tff(c_278, plain, (![A_144, B_145, C_146]: (v1_funct_2(k3_filter_1(A_144, B_145, C_146), k2_zfmisc_1(k8_eqrel_1(A_144, B_145), k8_eqrel_1(A_144, B_145)), k8_eqrel_1(A_144, B_145)) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_144, A_144), A_144))) | ~v1_funct_2(C_146, k2_zfmisc_1(A_144, A_144), A_144) | ~v1_funct_1(C_146) | ~m1_subset_1(B_145, k1_zfmisc_1(k2_zfmisc_1(A_144, A_144))) | ~v8_relat_2(B_145) | ~v3_relat_2(B_145) | ~v1_partfun1(B_145, A_144) | v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.64  tff(c_281, plain, (![C_146]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_146), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_146, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_146) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_278])).
% 3.88/1.64  tff(c_289, plain, (![C_146]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_146), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_146, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_146) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_158, c_158, c_281])).
% 3.88/1.64  tff(c_290, plain, (![C_146]: (v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_146), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_146, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_146))), inference(negUnitSimplification, [status(thm)], [c_60, c_289])).
% 3.88/1.64  tff(c_298, plain, (![A_148, B_149, C_150]: (m1_subset_1(k3_filter_1(A_148, B_149, C_150), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_148, B_149), k8_eqrel_1(A_148, B_149)), k8_eqrel_1(A_148, B_149)))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_148, A_148), A_148))) | ~v1_funct_2(C_150, k2_zfmisc_1(A_148, A_148), A_148) | ~v1_funct_1(C_150) | ~m1_subset_1(B_149, k1_zfmisc_1(k2_zfmisc_1(A_148, A_148))) | ~v8_relat_2(B_149) | ~v3_relat_2(B_149) | ~v1_partfun1(B_149, A_148) | v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.88/1.64  tff(c_313, plain, (![C_150]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_150), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k8_eqrel_1('#skF_1', '#skF_2')), k8_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_150, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_150) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_298])).
% 3.88/1.64  tff(c_328, plain, (![C_150]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_150), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_150, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_150) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_158, c_158, c_313])).
% 3.88/1.64  tff(c_336, plain, (![C_151]: (m1_subset_1(k3_filter_1('#skF_1', '#skF_2', C_151), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')))) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_151, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_151))), inference(negUnitSimplification, [status(thm)], [c_60, c_328])).
% 3.88/1.64  tff(c_12, plain, (![A_13, B_14, C_16]: (r3_binop_1(A_13, B_14, C_16) | ~r2_binop_1(A_13, B_14, C_16) | ~r1_binop_1(A_13, B_14, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_13, A_13), A_13))) | ~v1_funct_2(C_16, k2_zfmisc_1(A_13, A_13), A_13) | ~v1_funct_1(C_16) | ~m1_subset_1(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.88/1.64  tff(c_460, plain, (![B_180, C_181]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_180, k3_filter_1('#skF_1', '#skF_2', C_181)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_180, k3_filter_1('#skF_1', '#skF_2', C_181)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_180, k3_filter_1('#skF_1', '#skF_2', C_181)) | ~v1_funct_2(k3_filter_1('#skF_1', '#skF_2', C_181), k2_zfmisc_1(k7_eqrel_1('#skF_1', '#skF_2'), k7_eqrel_1('#skF_1', '#skF_2')), k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_181)) | ~m1_subset_1(B_180, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_181, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_181))), inference(resolution, [status(thm)], [c_336, c_12])).
% 3.88/1.64  tff(c_464, plain, (![B_182, C_183]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', C_183)) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', C_183)) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', C_183)) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', C_183)) | ~m1_subset_1(B_182, k7_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2(C_183, k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_290, c_460])).
% 3.88/1.64  tff(c_466, plain, (![B_182]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_182, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_182, k7_eqrel_1('#skF_1', '#skF_2')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_118, c_464])).
% 3.88/1.64  tff(c_470, plain, (![B_184]: (r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_184, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_184, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), B_184, k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(B_184, k7_eqrel_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_99, c_261, c_466])).
% 3.88/1.64  tff(c_44, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_226])).
% 3.88/1.64  tff(c_160, plain, (~r3_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_44])).
% 3.88/1.64  tff(c_484, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_470, c_160])).
% 3.88/1.64  tff(c_485, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k7_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_484])).
% 3.88/1.64  tff(c_488, plain, (~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_221, c_485])).
% 3.88/1.64  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_488])).
% 3.88/1.64  tff(c_493, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_484])).
% 3.88/1.64  tff(c_495, plain, (~r2_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_493])).
% 3.88/1.64  tff(c_517, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_268, c_495])).
% 3.88/1.64  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_172, c_517])).
% 3.88/1.64  tff(c_522, plain, (~r1_binop_1(k7_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_493])).
% 3.88/1.64  tff(c_526, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_276, c_522])).
% 3.88/1.64  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_178, c_526])).
% 3.88/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.64  
% 3.88/1.64  Inference rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Ref     : 0
% 3.88/1.64  #Sup     : 81
% 3.88/1.64  #Fact    : 0
% 3.88/1.64  #Define  : 0
% 3.88/1.64  #Split   : 9
% 3.88/1.64  #Chain   : 0
% 3.88/1.64  #Close   : 0
% 3.88/1.64  
% 3.88/1.64  Ordering : KBO
% 3.88/1.64  
% 3.88/1.64  Simplification rules
% 3.88/1.64  ----------------------
% 3.88/1.64  #Subsume      : 18
% 3.88/1.64  #Demod        : 198
% 3.88/1.64  #Tautology    : 11
% 3.88/1.64  #SimpNegUnit  : 38
% 3.88/1.64  #BackRed      : 2
% 3.88/1.64  
% 3.88/1.64  #Partial instantiations: 0
% 3.88/1.64  #Strategies tried      : 1
% 3.88/1.64  
% 3.88/1.64  Timing (in seconds)
% 3.88/1.64  ----------------------
% 3.88/1.64  Preprocessing        : 0.40
% 3.88/1.64  Parsing              : 0.22
% 3.88/1.64  CNF conversion       : 0.03
% 3.88/1.64  Main loop            : 0.40
% 3.88/1.64  Inferencing          : 0.14
% 3.88/1.64  Reduction            : 0.13
% 3.88/1.64  Demodulation         : 0.10
% 3.88/1.64  BG Simplification    : 0.02
% 3.88/1.64  Subsumption          : 0.08
% 3.88/1.64  Abstraction          : 0.02
% 3.88/1.64  MUC search           : 0.00
% 3.88/1.64  Cooper               : 0.00
% 3.88/1.64  Total                : 0.86
% 3.88/1.64  Index Insertion      : 0.00
% 3.88/1.64  Index Deletion       : 0.00
% 3.88/1.64  Index Matching       : 0.00
% 3.88/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
