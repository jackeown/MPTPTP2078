%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:55 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  152 (1192 expanded)
%              Number of leaves         :   47 ( 468 expanded)
%              Depth                    :   15
%              Number of atoms          :  479 (5164 expanded)
%              Number of equality atoms :   10 ( 146 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > r2_hidden > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k7_eqrel_1,type,(
    k7_eqrel_1: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k9_eqrel_1,type,(
    k9_eqrel_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_binop_1,type,(
    r3_binop_1: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(r1_binop_1,type,(
    r1_binop_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_127,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_245,negated_conjecture,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_52,axiom,(
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

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => k9_eqrel_1(A,B,C) = k11_relat_1(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_eqrel_1)).

tff(f_222,axiom,(
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

tff(f_200,axiom,(
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

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_subset_1(k7_eqrel_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_eqrel_1(B,A)
         => ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

tff(f_171,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_178,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_165,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_75,axiom,(
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

tff(c_30,plain,(
    ! [A_25] : m1_subset_1('#skF_1'(A_25),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    m2_filter_1('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_54,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_68,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_68])).

tff(c_94,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_funct_1(C_97)
      | ~ m2_filter_1(C_97,A_98,B_99)
      | ~ v1_relat_1(B_99)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_97,plain,
    ( v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_100,plain,
    ( v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_97])).

tff(c_101,plain,(
    v1_funct_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_100])).

tff(c_108,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_funct_2(C_103,k2_zfmisc_1(A_104,A_104),A_104)
      | ~ m2_filter_1(C_103,A_104,B_105)
      | ~ v1_relat_1(B_105)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_110,plain,
    ( v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_108])).

tff(c_113,plain,
    ( v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_110])).

tff(c_114,plain,(
    v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_113])).

tff(c_127,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_113,A_113),A_113)))
      | ~ m2_filter_1(C_112,A_113,B_114)
      | ~ v1_relat_1(B_114)
      | v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_129,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_127])).

tff(c_132,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_129])).

tff(c_133,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_132])).

tff(c_50,plain,(
    r3_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_279,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_binop_1(A_138,B_139,C_140)
      | ~ r3_binop_1(A_138,B_139,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_138,A_138),A_138)))
      | ~ v1_funct_2(C_140,k2_zfmisc_1(A_138,A_138),A_138)
      | ~ v1_funct_1(C_140)
      | ~ m1_subset_1(B_139,A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_281,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_279])).

tff(c_284,plain,(
    r2_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_101,c_114,c_133,c_281])).

tff(c_62,plain,(
    v1_partfun1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_60,plain,(
    v3_relat_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_58,plain,(
    v8_relat_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_169,plain,(
    ! [A_119,B_120] :
      ( k8_eqrel_1(A_119,B_120) = k7_eqrel_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v1_partfun1(B_120,A_119)
      | ~ v8_relat_2(B_120)
      | ~ v3_relat_2(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_172,plain,
    ( k8_eqrel_1('#skF_2','#skF_3') = k7_eqrel_1('#skF_2','#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_169])).

tff(c_179,plain,(
    k8_eqrel_1('#skF_2','#skF_3') = k7_eqrel_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_172])).

tff(c_207,plain,(
    ! [A_126,B_127,C_128] :
      ( k9_eqrel_1(A_126,B_127,C_128) = k11_relat_1(B_127,C_128)
      | ~ m1_subset_1(C_128,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1(A_126,A_126)))
      | ~ v1_partfun1(B_127,A_126)
      | ~ v8_relat_2(B_127)
      | ~ v3_relat_2(B_127)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_217,plain,(
    ! [B_127] :
      ( k9_eqrel_1('#skF_2',B_127,'#skF_4') = k11_relat_1(B_127,'#skF_4')
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_partfun1(B_127,'#skF_2')
      | ~ v8_relat_2(B_127)
      | ~ v3_relat_2(B_127)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_207])).

tff(c_225,plain,(
    ! [B_129] :
      ( k9_eqrel_1('#skF_2',B_129,'#skF_4') = k11_relat_1(B_129,'#skF_4')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v1_partfun1(B_129,'#skF_2')
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_217])).

tff(c_228,plain,
    ( k9_eqrel_1('#skF_2','#skF_3','#skF_4') = k11_relat_1('#skF_3','#skF_4')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_225])).

tff(c_235,plain,(
    k9_eqrel_1('#skF_2','#skF_3','#skF_4') = k11_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_228])).

tff(c_446,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( r2_binop_1(k8_eqrel_1(A_160,B_161),k9_eqrel_1(A_160,B_161,C_162),k3_filter_1(A_160,B_161,D_163))
      | ~ r2_binop_1(A_160,C_162,D_163)
      | ~ m2_filter_1(D_163,A_160,B_161)
      | ~ m1_subset_1(C_162,A_160)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_zfmisc_1(A_160,A_160)))
      | ~ v8_relat_2(B_161)
      | ~ v3_relat_2(B_161)
      | ~ v1_partfun1(B_161,A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_452,plain,(
    ! [D_163] :
      ( r2_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_163))
      | ~ r2_binop_1('#skF_2','#skF_4',D_163)
      | ~ m2_filter_1(D_163,'#skF_2','#skF_3')
      | ~ m1_subset_1('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2('#skF_3')
      | ~ v3_relat_2('#skF_3')
      | ~ v1_partfun1('#skF_3','#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_446])).

tff(c_460,plain,(
    ! [D_163] :
      ( r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_163))
      | ~ r2_binop_1('#skF_2','#skF_4',D_163)
      | ~ m2_filter_1(D_163,'#skF_2','#skF_3')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_179,c_452])).

tff(c_461,plain,(
    ! [D_163] :
      ( r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_163))
      | ~ r2_binop_1('#skF_2','#skF_4',D_163)
      | ~ m2_filter_1(D_163,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_460])).

tff(c_260,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_binop_1(A_132,B_133,C_134)
      | ~ r3_binop_1(A_132,B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_132,A_132),A_132)))
      | ~ v1_funct_2(C_134,k2_zfmisc_1(A_132,A_132),A_132)
      | ~ v1_funct_1(C_134)
      | ~ m1_subset_1(B_133,A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_260])).

tff(c_265,plain,(
    r1_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_101,c_114,c_133,c_262])).

tff(c_497,plain,(
    ! [A_173,B_174,C_175,D_176] :
      ( r1_binop_1(k8_eqrel_1(A_173,B_174),k9_eqrel_1(A_173,B_174,C_175),k3_filter_1(A_173,B_174,D_176))
      | ~ r1_binop_1(A_173,C_175,D_176)
      | ~ m2_filter_1(D_176,A_173,B_174)
      | ~ m1_subset_1(C_175,A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(k2_zfmisc_1(A_173,A_173)))
      | ~ v8_relat_2(B_174)
      | ~ v3_relat_2(B_174)
      | ~ v1_partfun1(B_174,A_173)
      | v1_xboole_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_503,plain,(
    ! [D_176] :
      ( r1_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_176))
      | ~ r1_binop_1('#skF_2','#skF_4',D_176)
      | ~ m2_filter_1(D_176,'#skF_2','#skF_3')
      | ~ m1_subset_1('#skF_4','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2('#skF_3')
      | ~ v3_relat_2('#skF_3')
      | ~ v1_partfun1('#skF_3','#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_497])).

tff(c_511,plain,(
    ! [D_176] :
      ( r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_176))
      | ~ r1_binop_1('#skF_2','#skF_4',D_176)
      | ~ m2_filter_1(D_176,'#skF_2','#skF_3')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_54,c_179,c_503])).

tff(c_512,plain,(
    ! [D_176] :
      ( r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3',D_176))
      | ~ r1_binop_1('#skF_2','#skF_4',D_176)
      | ~ m2_filter_1(D_176,'#skF_2','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_511])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k7_eqrel_1(A_14,B_15),k1_zfmisc_1(k1_zfmisc_1(A_14)))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k2_zfmisc_1(A_14,A_14)))
      | ~ v1_partfun1(B_15,A_14)
      | ~ v8_relat_2(B_15)
      | ~ v3_relat_2(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_151,plain,(
    ! [A_117,B_118] :
      ( m1_eqrel_1(k8_eqrel_1(A_117,B_118),A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(k2_zfmisc_1(A_117,A_117)))
      | ~ v1_partfun1(B_118,A_117)
      | ~ v8_relat_2(B_118)
      | ~ v3_relat_2(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_154,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_151])).

tff(c_161,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_154])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( ~ v1_xboole_0(B_3)
      | ~ m1_eqrel_1(B_3,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,
    ( ~ v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_168,plain,(
    ~ v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_165])).

tff(c_181,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_168])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( r2_hidden(A_36,B_37)
      | v1_xboole_0(B_37)
      | ~ m1_subset_1(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_195,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k7_eqrel_1(A_121,B_122),k1_zfmisc_1(k1_zfmisc_1(A_121)))
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121)))
      | ~ v1_partfun1(B_122,A_121)
      | ~ v8_relat_2(B_122)
      | ~ v3_relat_2(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [C_40,B_39,A_38] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_202,plain,(
    ! [A_123,A_124,B_125] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_123))
      | ~ r2_hidden(A_124,k7_eqrel_1(A_123,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1(A_123,A_123)))
      | ~ v1_partfun1(B_125,A_123)
      | ~ v8_relat_2(B_125)
      | ~ v3_relat_2(B_125) ) ),
    inference(resolution,[status(thm)],[c_195,c_42])).

tff(c_266,plain,(
    ! [A_135,B_136,A_137] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_135))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_135,A_135)))
      | ~ v1_partfun1(B_136,A_135)
      | ~ v8_relat_2(B_136)
      | ~ v3_relat_2(B_136)
      | v1_xboole_0(k7_eqrel_1(A_135,B_136))
      | ~ m1_subset_1(A_137,k7_eqrel_1(A_135,B_136)) ) ),
    inference(resolution,[status(thm)],[c_40,c_202])).

tff(c_268,plain,(
    ! [A_137] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ v1_partfun1('#skF_3','#skF_2')
      | ~ v8_relat_2('#skF_3')
      | ~ v3_relat_2('#skF_3')
      | v1_xboole_0(k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(A_137,k7_eqrel_1('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_56,c_266])).

tff(c_274,plain,(
    ! [A_137] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | v1_xboole_0(k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(A_137,k7_eqrel_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_268])).

tff(c_275,plain,(
    ! [A_137] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(A_137,k7_eqrel_1('#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_274])).

tff(c_277,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_285,plain,(
    ! [A_141,B_142,C_143] :
      ( m2_subset_1(k9_eqrel_1(A_141,B_142,C_143),k1_zfmisc_1(A_141),k8_eqrel_1(A_141,B_142))
      | ~ m1_subset_1(C_143,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v1_partfun1(B_142,A_141)
      | ~ v8_relat_2(B_142)
      | ~ v3_relat_2(B_142)
      | v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_293,plain,
    ( m2_subset_1(k11_relat_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'),k8_eqrel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_285])).

tff(c_302,plain,
    ( m2_subset_1(k11_relat_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'),k7_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_56,c_54,c_179,c_293])).

tff(c_303,plain,(
    m2_subset_1(k11_relat_1('#skF_3','#skF_4'),k1_zfmisc_1('#skF_2'),k7_eqrel_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_302])).

tff(c_36,plain,(
    ! [C_35,B_33,A_32] :
      ( m1_subset_1(C_35,B_33)
      | ~ m2_subset_1(C_35,A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32))
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_318,plain,
    ( m1_subset_1(k11_relat_1('#skF_3','#skF_4'),k7_eqrel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | v1_xboole_0(k7_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_303,c_36])).

tff(c_321,plain,
    ( m1_subset_1(k11_relat_1('#skF_3','#skF_4'),k7_eqrel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_181,c_318])).

tff(c_344,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_347,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_344])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_62,c_56,c_347])).

tff(c_352,plain,(
    m1_subset_1(k11_relat_1('#skF_3','#skF_4'),k7_eqrel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_370,plain,(
    ! [A_148,B_149,C_150] :
      ( v1_funct_1(k3_filter_1(A_148,B_149,C_150))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_148,A_148),A_148)))
      | ~ v1_funct_2(C_150,k2_zfmisc_1(A_148,A_148),A_148)
      | ~ v1_funct_1(C_150)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1(A_148,A_148)))
      | ~ v8_relat_2(B_149)
      | ~ v3_relat_2(B_149)
      | ~ v1_partfun1(B_149,A_148)
      | v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_372,plain,(
    ! [B_149] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_149,'#skF_5'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_149)
      | ~ v3_relat_2(B_149)
      | ~ v1_partfun1(B_149,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_133,c_370])).

tff(c_378,plain,(
    ! [B_149] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_149,'#skF_5'))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_149)
      | ~ v3_relat_2(B_149)
      | ~ v1_partfun1(B_149,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_114,c_372])).

tff(c_406,plain,(
    ! [B_153] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_153,'#skF_5'))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_153)
      | ~ v3_relat_2(B_153)
      | ~ v1_partfun1(B_153,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_378])).

tff(c_409,plain,
    ( v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_406])).

tff(c_416,plain,(
    v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_409])).

tff(c_564,plain,(
    ! [A_186,B_187,C_188] :
      ( v1_funct_2(k3_filter_1(A_186,B_187,C_188),k2_zfmisc_1(k8_eqrel_1(A_186,B_187),k8_eqrel_1(A_186,B_187)),k8_eqrel_1(A_186,B_187))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_186,A_186),A_186)))
      | ~ v1_funct_2(C_188,k2_zfmisc_1(A_186,A_186),A_186)
      | ~ v1_funct_1(C_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1(A_186,A_186)))
      | ~ v8_relat_2(B_187)
      | ~ v3_relat_2(B_187)
      | ~ v1_partfun1(B_187,A_186)
      | v1_xboole_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_567,plain,(
    ! [C_188] :
      ( v1_funct_2(k3_filter_1('#skF_2','#skF_3',C_188),k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k8_eqrel_1('#skF_2','#skF_3')),k8_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_188,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_188)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2('#skF_3')
      | ~ v3_relat_2('#skF_3')
      | ~ v1_partfun1('#skF_3','#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_564])).

tff(c_575,plain,(
    ! [C_188] :
      ( v1_funct_2(k3_filter_1('#skF_2','#skF_3',C_188),k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k7_eqrel_1('#skF_2','#skF_3')),k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_188,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_188)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_179,c_179,c_567])).

tff(c_576,plain,(
    ! [C_188] :
      ( v1_funct_2(k3_filter_1('#skF_2','#skF_3',C_188),k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k7_eqrel_1('#skF_2','#skF_3')),k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_188,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_575])).

tff(c_591,plain,(
    ! [A_195,B_196,C_197] :
      ( m1_subset_1(k3_filter_1(A_195,B_196,C_197),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_195,B_196),k8_eqrel_1(A_195,B_196)),k8_eqrel_1(A_195,B_196))))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_195,A_195),A_195)))
      | ~ v1_funct_2(C_197,k2_zfmisc_1(A_195,A_195),A_195)
      | ~ v1_funct_1(C_197)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(A_195,A_195)))
      | ~ v8_relat_2(B_196)
      | ~ v3_relat_2(B_196)
      | ~ v1_partfun1(B_196,A_195)
      | v1_xboole_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_607,plain,(
    ! [C_197] :
      ( m1_subset_1(k3_filter_1('#skF_2','#skF_3',C_197),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k8_eqrel_1('#skF_2','#skF_3')),k8_eqrel_1('#skF_2','#skF_3'))))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_197,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_197)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2('#skF_3')
      | ~ v3_relat_2('#skF_3')
      | ~ v1_partfun1('#skF_3','#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_591])).

tff(c_621,plain,(
    ! [C_197] :
      ( m1_subset_1(k3_filter_1('#skF_2','#skF_3',C_197),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k7_eqrel_1('#skF_2','#skF_3')),k7_eqrel_1('#skF_2','#skF_3'))))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_197,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_197)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_179,c_179,c_607])).

tff(c_629,plain,(
    ! [C_198] :
      ( m1_subset_1(k3_filter_1('#skF_2','#skF_3',C_198),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k7_eqrel_1('#skF_2','#skF_3')),k7_eqrel_1('#skF_2','#skF_3'))))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_198,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_621])).

tff(c_6,plain,(
    ! [A_7,B_8,C_10] :
      ( r3_binop_1(A_7,B_8,C_10)
      | ~ r2_binop_1(A_7,B_8,C_10)
      | ~ r1_binop_1(A_7,B_8,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_7,A_7),A_7)))
      | ~ v1_funct_2(C_10,k2_zfmisc_1(A_7,A_7),A_7)
      | ~ v1_funct_1(C_10)
      | ~ m1_subset_1(B_8,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_726,plain,(
    ! [B_217,C_218] :
      ( r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_217,k3_filter_1('#skF_2','#skF_3',C_218))
      | ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_217,k3_filter_1('#skF_2','#skF_3',C_218))
      | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_217,k3_filter_1('#skF_2','#skF_3',C_218))
      | ~ v1_funct_2(k3_filter_1('#skF_2','#skF_3',C_218),k2_zfmisc_1(k7_eqrel_1('#skF_2','#skF_3'),k7_eqrel_1('#skF_2','#skF_3')),k7_eqrel_1('#skF_2','#skF_3'))
      | ~ v1_funct_1(k3_filter_1('#skF_2','#skF_3',C_218))
      | ~ m1_subset_1(B_217,k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_218,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_629,c_6])).

tff(c_730,plain,(
    ! [B_219,C_220] :
      ( r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3',C_220))
      | ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3',C_220))
      | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3',C_220))
      | ~ v1_funct_1(k3_filter_1('#skF_2','#skF_3',C_220))
      | ~ m1_subset_1(B_219,k7_eqrel_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
      | ~ v1_funct_2(C_220,k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1(C_220) ) ),
    inference(resolution,[status(thm)],[c_576,c_726])).

tff(c_732,plain,(
    ! [B_219] :
      ( r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_219,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(B_219,k7_eqrel_1('#skF_2','#skF_3'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_133,c_730])).

tff(c_740,plain,(
    ! [B_221] :
      ( r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_221,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_221,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),B_221,k3_filter_1('#skF_2','#skF_3','#skF_5'))
      | ~ m1_subset_1(B_221,k7_eqrel_1('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_114,c_416,c_732])).

tff(c_48,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_183,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_48])).

tff(c_238,plain,(
    ~ r3_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_183])).

tff(c_747,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k11_relat_1('#skF_3','#skF_4'),k7_eqrel_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_740,c_238])).

tff(c_756,plain,
    ( ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_747])).

tff(c_757,plain,(
    ~ r1_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_756])).

tff(c_760,plain,
    ( ~ r1_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m2_filter_1('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_512,c_757])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_265,c_760])).

tff(c_765,plain,(
    ~ r2_binop_1(k7_eqrel_1('#skF_2','#skF_3'),k11_relat_1('#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_756])).

tff(c_791,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m2_filter_1('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_461,c_765])).

tff(c_795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_284,c_791])).

tff(c_798,plain,(
    ! [A_226] : ~ m1_subset_1(A_226,k7_eqrel_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_803,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_30,c_798])).

%------------------------------------------------------------------------------
