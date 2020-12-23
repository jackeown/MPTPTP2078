%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1409+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:55 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  206 (4784 expanded)
%              Number of leaves         :   55 (1842 expanded)
%              Depth                    :   24
%              Number of atoms          :  768 (21933 expanded)
%              Number of equality atoms :   55 (2316 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m2_subset_1 > m2_filter_1 > v1_partfun1 > r2_hidden > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k6_eqrel_1 > k4_binop_1 > k9_eqrel_1 > k3_filter_1 > k1_binop_1 > k8_eqrel_1 > k7_eqrel_1 > k2_zfmisc_1 > k11_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_binop_1,type,(
    k4_binop_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k7_eqrel_1,type,(
    k7_eqrel_1: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_eqrel_1,type,(
    k9_eqrel_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_binop_1,type,(
    k1_binop_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k3_filter_1,type,(
    k3_filter_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_eqrel_1,type,(
    k6_eqrel_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(m2_filter_1,type,(
    m2_filter_1: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m2_subset_1,type,(
    m2_subset_1: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_163,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_267,negated_conjecture,(
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
                    ( m1_subset_1(D,A)
                   => ! [E] :
                        ( m2_filter_1(E,A,B)
                       => k1_binop_1(k3_filter_1(A,B,E),k6_eqrel_1(A,A,B,C),k6_eqrel_1(A,A,B,D)) = k6_eqrel_1(A,A,B,k4_binop_1(A,E,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_filter_1)).

tff(f_189,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k8_eqrel_1(A,B) = k7_eqrel_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_eqrel_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_eqrel_1(B,A)
         => ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_eqrel_1)).

tff(f_236,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_subset_1(k7_eqrel_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_eqrel_1)).

tff(f_204,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => k9_eqrel_1(A,B,C) = k11_relat_1(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_eqrel_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_217,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_243,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_111,axiom,(
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

tff(f_179,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_eqrel_1(A,B,C,D) = k11_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_eqrel_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v3_relat_2(A)
        & v8_relat_2(A) )
     => ( v1_relat_1(A)
        & v1_relat_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_partfun1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_230,axiom,(
    ! [A,B] :
      ( ( v1_relat_2(B)
        & v3_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,k6_eqrel_1(A,A,B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_eqrel_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( v1_partfun1(B,A)
            & v3_relat_2(B)
            & v8_relat_2(B)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,k2_zfmisc_1(A,A),A)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) )
             => ( m2_filter_1(C,A,B)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A,B),k8_eqrel_1(A,B)),k8_eqrel_1(A,B)))) )
                   => ( D = k3_filter_1(A,B,C)
                    <=> ! [E,F,G,H] :
                          ( ( r2_hidden(E,k8_eqrel_1(A,B))
                            & r2_hidden(F,k8_eqrel_1(A,B))
                            & r2_hidden(G,E)
                            & r2_hidden(H,F) )
                         => k1_binop_1(D,E,F) = k6_eqrel_1(A,A,B,k1_binop_1(C,G,H)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_filter_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_175,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,k2_zfmisc_1(A,A),A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A)))
        & m1_subset_1(C,A)
        & m1_subset_1(D,A) )
     => k4_binop_1(A,B,C,D) = k1_binop_1(B,C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_binop_1)).

tff(c_40,plain,(
    ! [A_161] : m1_subset_1('#skF_5'(A_161),A_161) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    v3_relat_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_70,plain,(
    v8_relat_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_74,plain,(
    v1_partfun1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_243,plain,(
    ! [A_265,B_266] :
      ( k8_eqrel_1(A_265,B_266) = k7_eqrel_1(A_265,B_266)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(k2_zfmisc_1(A_265,A_265)))
      | ~ v1_partfun1(B_266,A_265)
      | ~ v8_relat_2(B_266)
      | ~ v3_relat_2(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_246,plain,
    ( k8_eqrel_1('#skF_6','#skF_7') = k7_eqrel_1('#skF_6','#skF_7')
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_243])).

tff(c_253,plain,(
    k8_eqrel_1('#skF_6','#skF_7') = k7_eqrel_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_246])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_225,plain,(
    ! [A_263,B_264] :
      ( m1_eqrel_1(k8_eqrel_1(A_263,B_264),A_263)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k2_zfmisc_1(A_263,A_263)))
      | ~ v1_partfun1(B_264,A_263)
      | ~ v8_relat_2(B_264)
      | ~ v3_relat_2(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_228,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_6','#skF_7'),'#skF_6')
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_225])).

tff(c_235,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_228])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( ~ v1_xboole_0(B_3)
      | ~ m1_eqrel_1(B_3,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_239,plain,
    ( ~ v1_xboole_0(k8_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_235,c_2])).

tff(c_242,plain,(
    ~ v1_xboole_0(k8_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_239])).

tff(c_255,plain,(
    ~ v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_242])).

tff(c_56,plain,(
    ! [A_184,B_185] :
      ( r2_hidden(A_184,B_185)
      | v1_xboole_0(B_185)
      | ~ m1_subset_1(A_184,B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_28,plain,(
    ! [A_150,B_151] :
      ( m1_subset_1(k7_eqrel_1(A_150,B_151),k1_zfmisc_1(k1_zfmisc_1(A_150)))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k2_zfmisc_1(A_150,A_150)))
      | ~ v1_partfun1(B_151,A_150)
      | ~ v8_relat_2(B_151)
      | ~ v3_relat_2(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_292,plain,(
    ! [A_276,B_277,C_278] :
      ( k9_eqrel_1(A_276,B_277,C_278) = k11_relat_1(B_277,C_278)
      | ~ m1_subset_1(C_278,A_276)
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1(A_276,A_276)))
      | ~ v1_partfun1(B_277,A_276)
      | ~ v8_relat_2(B_277)
      | ~ v3_relat_2(B_277)
      | v1_xboole_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_302,plain,(
    ! [B_277] :
      ( k9_eqrel_1('#skF_6',B_277,'#skF_9') = k11_relat_1(B_277,'#skF_9')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_partfun1(B_277,'#skF_6')
      | ~ v8_relat_2(B_277)
      | ~ v3_relat_2(B_277)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_292])).

tff(c_315,plain,(
    ! [B_279] :
      ( k9_eqrel_1('#skF_6',B_279,'#skF_9') = k11_relat_1(B_279,'#skF_9')
      | ~ m1_subset_1(B_279,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_partfun1(B_279,'#skF_6')
      | ~ v8_relat_2(B_279)
      | ~ v3_relat_2(B_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_302])).

tff(c_318,plain,
    ( k9_eqrel_1('#skF_6','#skF_7','#skF_9') = k11_relat_1('#skF_7','#skF_9')
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_315])).

tff(c_325,plain,(
    k9_eqrel_1('#skF_6','#skF_7','#skF_9') = k11_relat_1('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_318])).

tff(c_364,plain,(
    ! [A_283,B_284,C_285] :
      ( m2_subset_1(k9_eqrel_1(A_283,B_284,C_285),k1_zfmisc_1(A_283),k8_eqrel_1(A_283,B_284))
      | ~ m1_subset_1(C_285,A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(k2_zfmisc_1(A_283,A_283)))
      | ~ v1_partfun1(B_284,A_283)
      | ~ v8_relat_2(B_284)
      | ~ v3_relat_2(B_284)
      | v1_xboole_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_375,plain,
    ( m2_subset_1(k11_relat_1('#skF_7','#skF_9'),k1_zfmisc_1('#skF_6'),k8_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_9','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_364])).

tff(c_387,plain,
    ( m2_subset_1(k11_relat_1('#skF_7','#skF_9'),k1_zfmisc_1('#skF_6'),k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_68,c_64,c_253,c_375])).

tff(c_388,plain,(
    m2_subset_1(k11_relat_1('#skF_7','#skF_9'),k1_zfmisc_1('#skF_6'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_387])).

tff(c_50,plain,(
    ! [C_179,B_177,A_176] :
      ( m1_subset_1(C_179,B_177)
      | ~ m2_subset_1(C_179,A_176,B_177)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(A_176))
      | v1_xboole_0(B_177)
      | v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_398,plain,
    ( m1_subset_1(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_388,c_50])).

tff(c_401,plain,
    ( m1_subset_1(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_398])).

tff(c_428,plain,(
    ~ m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_431,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_68,c_431])).

tff(c_437,plain,(
    m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_58,plain,(
    ! [C_188,B_187,A_186] :
      ( ~ v1_xboole_0(C_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(C_188))
      | ~ r2_hidden(A_186,B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_448,plain,(
    ! [A_186] :
      ( ~ v1_xboole_0(k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_186,k7_eqrel_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_437,c_58])).

tff(c_449,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_66,plain,(
    m1_subset_1('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_304,plain,(
    ! [B_277] :
      ( k9_eqrel_1('#skF_6',B_277,'#skF_8') = k11_relat_1(B_277,'#skF_8')
      | ~ m1_subset_1(B_277,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_partfun1(B_277,'#skF_6')
      | ~ v8_relat_2(B_277)
      | ~ v3_relat_2(B_277)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_292])).

tff(c_331,plain,(
    ! [B_280] :
      ( k9_eqrel_1('#skF_6',B_280,'#skF_8') = k11_relat_1(B_280,'#skF_8')
      | ~ m1_subset_1(B_280,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_partfun1(B_280,'#skF_6')
      | ~ v8_relat_2(B_280)
      | ~ v3_relat_2(B_280) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_304])).

tff(c_334,plain,
    ( k9_eqrel_1('#skF_6','#skF_7','#skF_8') = k11_relat_1('#skF_7','#skF_8')
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_331])).

tff(c_341,plain,(
    k9_eqrel_1('#skF_6','#skF_7','#skF_8') = k11_relat_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_334])).

tff(c_372,plain,
    ( m2_subset_1(k11_relat_1('#skF_7','#skF_8'),k1_zfmisc_1('#skF_6'),k8_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
    | ~ v1_partfun1('#skF_7','#skF_6')
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_364])).

tff(c_384,plain,
    ( m2_subset_1(k11_relat_1('#skF_7','#skF_8'),k1_zfmisc_1('#skF_6'),k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_74,c_68,c_66,c_253,c_372])).

tff(c_385,plain,(
    m2_subset_1(k11_relat_1('#skF_7','#skF_8'),k1_zfmisc_1('#skF_6'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_384])).

tff(c_393,plain,
    ( m1_subset_1(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_385,c_50])).

tff(c_396,plain,
    ( m1_subset_1(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k7_eqrel_1('#skF_6','#skF_7'),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_393])).

tff(c_490,plain,
    ( m1_subset_1(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0(k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_396])).

tff(c_491,plain,(
    m1_subset_1(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_490])).

tff(c_655,plain,(
    ! [A_308,B_309,C_310] :
      ( v1_funct_2(k3_filter_1(A_308,B_309,C_310),k2_zfmisc_1(k8_eqrel_1(A_308,B_309),k8_eqrel_1(A_308,B_309)),k8_eqrel_1(A_308,B_309))
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_308,A_308),A_308)))
      | ~ v1_funct_2(C_310,k2_zfmisc_1(A_308,A_308),A_308)
      | ~ v1_funct_1(C_310)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k2_zfmisc_1(A_308,A_308)))
      | ~ v8_relat_2(B_309)
      | ~ v3_relat_2(B_309)
      | ~ v1_partfun1(B_309,A_308)
      | v1_xboole_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_658,plain,(
    ! [C_310] :
      ( v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_310),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_310,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_310)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2('#skF_7')
      | ~ v3_relat_2('#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_655])).

tff(c_666,plain,(
    ! [C_310] :
      ( v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_310),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_310,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_310)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_253,c_253,c_658])).

tff(c_667,plain,(
    ! [C_310] :
      ( v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_310),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_310,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_310) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_666])).

tff(c_717,plain,(
    ! [A_315,B_316,C_317] :
      ( m1_subset_1(k3_filter_1(A_315,B_316,C_317),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_315,B_316),k8_eqrel_1(A_315,B_316)),k8_eqrel_1(A_315,B_316))))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_315,A_315),A_315)))
      | ~ v1_funct_2(C_317,k2_zfmisc_1(A_315,A_315),A_315)
      | ~ v1_funct_1(C_317)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k2_zfmisc_1(A_315,A_315)))
      | ~ v8_relat_2(B_316)
      | ~ v3_relat_2(B_316)
      | ~ v1_partfun1(B_316,A_315)
      | v1_xboole_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_735,plain,(
    ! [C_317] :
      ( m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_317),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_317,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_317)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2('#skF_7')
      | ~ v3_relat_2('#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_717])).

tff(c_750,plain,(
    ! [C_317] :
      ( m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_317),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_317,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_317)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_253,c_253,c_735])).

tff(c_751,plain,(
    ! [C_317] :
      ( m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_317),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_317,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_750])).

tff(c_149,plain,(
    ! [A_242,B_243,C_244,D_245] :
      ( k6_eqrel_1(A_242,B_243,C_244,D_245) = k11_relat_1(C_244,D_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_155,plain,(
    ! [D_245] : k6_eqrel_1('#skF_6','#skF_6','#skF_7',D_245) = k11_relat_1('#skF_7',D_245) ),
    inference(resolution,[status(thm)],[c_68,c_149])).

tff(c_80,plain,(
    ! [A_220] :
      ( v1_relat_2(A_220)
      | ~ v8_relat_2(A_220)
      | ~ v3_relat_2(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_83,plain,
    ( v1_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_80])).

tff(c_86,plain,
    ( v1_relat_2('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_83])).

tff(c_87,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_88,plain,(
    ! [C_221,A_222,B_223] :
      ( v1_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_88])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_91])).

tff(c_100,plain,(
    v1_relat_2('#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_275,plain,(
    ! [C_269,A_270,B_271] :
      ( r2_hidden(C_269,k6_eqrel_1(A_270,A_270,B_271,C_269))
      | ~ r2_hidden(C_269,A_270)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(k2_zfmisc_1(A_270,A_270)))
      | ~ v1_partfun1(B_271,A_270)
      | ~ v3_relat_2(B_271)
      | ~ v1_relat_2(B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_277,plain,(
    ! [C_269] :
      ( r2_hidden(C_269,k6_eqrel_1('#skF_6','#skF_6','#skF_7',C_269))
      | ~ r2_hidden(C_269,'#skF_6')
      | ~ v1_partfun1('#skF_7','#skF_6')
      | ~ v3_relat_2('#skF_7')
      | ~ v1_relat_2('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_275])).

tff(c_283,plain,(
    ! [C_269] :
      ( r2_hidden(C_269,k11_relat_1('#skF_7',C_269))
      | ~ r2_hidden(C_269,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_72,c_74,c_155,c_277])).

tff(c_1096,plain,(
    ! [H_397,A_396,E_398,B_400,G_399,F_394,C_395] :
      ( k6_eqrel_1(A_396,A_396,B_400,k1_binop_1(C_395,G_399,H_397)) = k1_binop_1(k3_filter_1(A_396,B_400,C_395),E_398,F_394)
      | ~ r2_hidden(H_397,F_394)
      | ~ r2_hidden(G_399,E_398)
      | ~ r2_hidden(F_394,k8_eqrel_1(A_396,B_400))
      | ~ r2_hidden(E_398,k8_eqrel_1(A_396,B_400))
      | ~ m1_subset_1(k3_filter_1(A_396,B_400,C_395),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_396,B_400),k8_eqrel_1(A_396,B_400)),k8_eqrel_1(A_396,B_400))))
      | ~ v1_funct_2(k3_filter_1(A_396,B_400,C_395),k2_zfmisc_1(k8_eqrel_1(A_396,B_400),k8_eqrel_1(A_396,B_400)),k8_eqrel_1(A_396,B_400))
      | ~ v1_funct_1(k3_filter_1(A_396,B_400,C_395))
      | ~ m2_filter_1(C_395,A_396,B_400)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_396,A_396),A_396)))
      | ~ v1_funct_2(C_395,k2_zfmisc_1(A_396,A_396),A_396)
      | ~ v1_funct_1(C_395)
      | ~ m1_subset_1(B_400,k1_zfmisc_1(k2_zfmisc_1(A_396,A_396)))
      | ~ v8_relat_2(B_400)
      | ~ v3_relat_2(B_400)
      | ~ v1_partfun1(B_400,A_396)
      | v1_xboole_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1598,plain,(
    ! [A_521,G_519,C_522,B_518,B_523,E_517,A_520] :
      ( k6_eqrel_1(A_520,A_520,B_518,k1_binop_1(C_522,G_519,A_521)) = k1_binop_1(k3_filter_1(A_520,B_518,C_522),E_517,B_523)
      | ~ r2_hidden(G_519,E_517)
      | ~ r2_hidden(B_523,k8_eqrel_1(A_520,B_518))
      | ~ r2_hidden(E_517,k8_eqrel_1(A_520,B_518))
      | ~ m1_subset_1(k3_filter_1(A_520,B_518,C_522),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_520,B_518),k8_eqrel_1(A_520,B_518)),k8_eqrel_1(A_520,B_518))))
      | ~ v1_funct_2(k3_filter_1(A_520,B_518,C_522),k2_zfmisc_1(k8_eqrel_1(A_520,B_518),k8_eqrel_1(A_520,B_518)),k8_eqrel_1(A_520,B_518))
      | ~ v1_funct_1(k3_filter_1(A_520,B_518,C_522))
      | ~ m2_filter_1(C_522,A_520,B_518)
      | ~ m1_subset_1(C_522,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_520,A_520),A_520)))
      | ~ v1_funct_2(C_522,k2_zfmisc_1(A_520,A_520),A_520)
      | ~ v1_funct_1(C_522)
      | ~ m1_subset_1(B_518,k1_zfmisc_1(k2_zfmisc_1(A_520,A_520)))
      | ~ v8_relat_2(B_518)
      | ~ v3_relat_2(B_518)
      | ~ v1_partfun1(B_518,A_520)
      | v1_xboole_0(A_520)
      | v1_xboole_0(B_523)
      | ~ m1_subset_1(A_521,B_523) ) ),
    inference(resolution,[status(thm)],[c_56,c_1096])).

tff(c_2222,plain,(
    ! [C_641,B_638,C_640,A_639,A_637,B_636] :
      ( k6_eqrel_1(A_637,A_637,B_636,k1_binop_1(C_640,C_641,A_639)) = k1_binop_1(k3_filter_1(A_637,B_636,C_640),k11_relat_1('#skF_7',C_641),B_638)
      | ~ r2_hidden(B_638,k8_eqrel_1(A_637,B_636))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_641),k8_eqrel_1(A_637,B_636))
      | ~ m1_subset_1(k3_filter_1(A_637,B_636,C_640),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_637,B_636),k8_eqrel_1(A_637,B_636)),k8_eqrel_1(A_637,B_636))))
      | ~ v1_funct_2(k3_filter_1(A_637,B_636,C_640),k2_zfmisc_1(k8_eqrel_1(A_637,B_636),k8_eqrel_1(A_637,B_636)),k8_eqrel_1(A_637,B_636))
      | ~ v1_funct_1(k3_filter_1(A_637,B_636,C_640))
      | ~ m2_filter_1(C_640,A_637,B_636)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_637,A_637),A_637)))
      | ~ v1_funct_2(C_640,k2_zfmisc_1(A_637,A_637),A_637)
      | ~ v1_funct_1(C_640)
      | ~ m1_subset_1(B_636,k1_zfmisc_1(k2_zfmisc_1(A_637,A_637)))
      | ~ v8_relat_2(B_636)
      | ~ v3_relat_2(B_636)
      | ~ v1_partfun1(B_636,A_637)
      | v1_xboole_0(A_637)
      | v1_xboole_0(B_638)
      | ~ m1_subset_1(A_639,B_638)
      | ~ r2_hidden(C_641,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_283,c_1598])).

tff(c_2226,plain,(
    ! [C_640,C_641,A_639,B_638] :
      ( k6_eqrel_1('#skF_6','#skF_6','#skF_7',k1_binop_1(C_640,C_641,A_639)) = k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_640),k11_relat_1('#skF_7',C_641),B_638)
      | ~ r2_hidden(B_638,k8_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_641),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_640),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_640),k2_zfmisc_1(k8_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_640))
      | ~ m2_filter_1(C_640,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_640,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_640)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2('#skF_7')
      | ~ v3_relat_2('#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_6')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_638)
      | ~ m1_subset_1(A_639,B_638)
      | ~ r2_hidden(C_641,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_2222])).

tff(c_2231,plain,(
    ! [C_640,C_641,B_638,A_639] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_640),k11_relat_1('#skF_7',C_641),B_638) = k11_relat_1('#skF_7',k1_binop_1(C_640,C_641,A_639))
      | ~ r2_hidden(B_638,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_641),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_640),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_640),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_640))
      | ~ m2_filter_1(C_640,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_640,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_640)
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_638)
      | ~ m1_subset_1(A_639,B_638)
      | ~ r2_hidden(C_641,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_253,c_253,c_253,c_253,c_253,c_253,c_253,c_155,c_2226])).

tff(c_2234,plain,(
    ! [C_642,C_643,B_644,A_645] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_642),k11_relat_1('#skF_7',C_643),B_644) = k11_relat_1('#skF_7',k1_binop_1(C_642,C_643,A_645))
      | ~ r2_hidden(B_644,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_643),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_642),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_642),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_642))
      | ~ m2_filter_1(C_642,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_642,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_642)
      | v1_xboole_0(B_644)
      | ~ m1_subset_1(A_645,B_644)
      | ~ r2_hidden(C_643,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2231])).

tff(c_2239,plain,(
    ! [C_642,C_643,B_644,A_645] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_642),k11_relat_1('#skF_7',C_643),B_644) = k11_relat_1('#skF_7',k1_binop_1(C_642,C_643,A_645))
      | ~ r2_hidden(B_644,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_642),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_642),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_642))
      | ~ m2_filter_1(C_642,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_642,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_642,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_642)
      | v1_xboole_0(B_644)
      | ~ m1_subset_1(A_645,B_644)
      | ~ r2_hidden(C_643,'#skF_6')
      | v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k11_relat_1('#skF_7',C_643),k7_eqrel_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_56,c_2234])).

tff(c_2298,plain,(
    ! [C_659,C_660,B_661,A_662] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_659),k11_relat_1('#skF_7',C_660),B_661) = k11_relat_1('#skF_7',k1_binop_1(C_659,C_660,A_662))
      | ~ r2_hidden(B_661,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_659),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_659),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_659))
      | ~ m2_filter_1(C_659,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_659,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_659,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_659)
      | v1_xboole_0(B_661)
      | ~ m1_subset_1(A_662,B_661)
      | ~ r2_hidden(C_660,'#skF_6')
      | ~ m1_subset_1(k11_relat_1('#skF_7',C_660),k7_eqrel_1('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_2239])).

tff(c_2302,plain,(
    ! [C_663,C_664,B_665,A_666] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_663),k11_relat_1('#skF_7',C_664),B_665) = k11_relat_1('#skF_7',k1_binop_1(C_663,C_664,A_666))
      | ~ r2_hidden(B_665,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_663),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_663))
      | ~ m2_filter_1(C_663,'#skF_6','#skF_7')
      | v1_xboole_0(B_665)
      | ~ m1_subset_1(A_666,B_665)
      | ~ r2_hidden(C_664,'#skF_6')
      | ~ m1_subset_1(k11_relat_1('#skF_7',C_664),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_663,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_663) ) ),
    inference(resolution,[status(thm)],[c_751,c_2298])).

tff(c_2306,plain,(
    ! [C_667,C_668,B_669,A_670] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_667),k11_relat_1('#skF_7',C_668),B_669) = k11_relat_1('#skF_7',k1_binop_1(C_667,C_668,A_670))
      | ~ r2_hidden(B_669,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_667))
      | ~ m2_filter_1(C_667,'#skF_6','#skF_7')
      | v1_xboole_0(B_669)
      | ~ m1_subset_1(A_670,B_669)
      | ~ r2_hidden(C_668,'#skF_6')
      | ~ m1_subset_1(k11_relat_1('#skF_7',C_668),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_667,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_667,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_667) ) ),
    inference(resolution,[status(thm)],[c_667,c_2302])).

tff(c_2371,plain,(
    ! [C_671,C_672,A_673] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_671),k11_relat_1('#skF_7',C_672),A_673) = k11_relat_1('#skF_7',k1_binop_1(C_671,C_672,'#skF_5'(A_673)))
      | ~ r2_hidden(A_673,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_671))
      | ~ m2_filter_1(C_671,'#skF_6','#skF_7')
      | v1_xboole_0(A_673)
      | ~ r2_hidden(C_672,'#skF_6')
      | ~ m1_subset_1(k11_relat_1('#skF_7',C_672),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_671,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_671) ) ),
    inference(resolution,[status(thm)],[c_40,c_2306])).

tff(c_2381,plain,(
    ! [C_671,A_673] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_671),k11_relat_1('#skF_7','#skF_8'),A_673) = k11_relat_1('#skF_7',k1_binop_1(C_671,'#skF_8','#skF_5'(A_673)))
      | ~ r2_hidden(A_673,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_671))
      | ~ m2_filter_1(C_671,'#skF_6','#skF_7')
      | v1_xboole_0(A_673)
      | ~ r2_hidden('#skF_8','#skF_6')
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_671,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_671) ) ),
    inference(resolution,[status(thm)],[c_491,c_2371])).

tff(c_2383,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2381])).

tff(c_2386,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2383])).

tff(c_2389,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2386])).

tff(c_2391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2389])).

tff(c_2393,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2381])).

tff(c_436,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_6'))
    | m1_subset_1(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_472,plain,(
    m1_subset_1(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_436])).

tff(c_2382,plain,(
    ! [C_671,A_673] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_671),k11_relat_1('#skF_7','#skF_9'),A_673) = k11_relat_1('#skF_7',k1_binop_1(C_671,'#skF_9','#skF_5'(A_673)))
      | ~ r2_hidden(A_673,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_671))
      | ~ m2_filter_1(C_671,'#skF_6','#skF_7')
      | v1_xboole_0(A_673)
      | ~ r2_hidden('#skF_9','#skF_6')
      | ~ m1_subset_1(C_671,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_671,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_671) ) ),
    inference(resolution,[status(thm)],[c_472,c_2371])).

tff(c_2466,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2382])).

tff(c_2469,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2466])).

tff(c_2472,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2469])).

tff(c_2474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2472])).

tff(c_2476,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_2382])).

tff(c_101,plain,(
    v1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_62,plain,(
    m2_filter_1('#skF_10','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_129,plain,(
    ! [C_234,A_235,B_236] :
      ( v1_funct_1(C_234)
      | ~ m2_filter_1(C_234,A_235,B_236)
      | ~ v1_relat_1(B_236)
      | v1_xboole_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_132,plain,
    ( v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_129])).

tff(c_135,plain,
    ( v1_funct_1('#skF_10')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_132])).

tff(c_136,plain,(
    v1_funct_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_135])).

tff(c_137,plain,(
    ! [C_237,A_238,B_239] :
      ( v1_funct_2(C_237,k2_zfmisc_1(A_238,A_238),A_238)
      | ~ m2_filter_1(C_237,A_238,B_239)
      | ~ v1_relat_1(B_239)
      | v1_xboole_0(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_139,plain,
    ( v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
    | ~ v1_relat_1('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_137])).

tff(c_142,plain,
    ( v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_139])).

tff(c_143,plain,(
    v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_142])).

tff(c_180,plain,(
    ! [C_254,A_255,B_256] :
      ( m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_255,A_255),A_255)))
      | ~ m2_filter_1(C_254,A_255,B_256)
      | ~ v1_relat_1(B_256)
      | v1_xboole_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_182,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
    | ~ v1_relat_1('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_185,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_182])).

tff(c_186,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_185])).

tff(c_576,plain,(
    ! [A_299,B_300,C_301] :
      ( v1_funct_1(k3_filter_1(A_299,B_300,C_301))
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_299,A_299),A_299)))
      | ~ v1_funct_2(C_301,k2_zfmisc_1(A_299,A_299),A_299)
      | ~ v1_funct_1(C_301)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_zfmisc_1(A_299,A_299)))
      | ~ v8_relat_2(B_300)
      | ~ v3_relat_2(B_300)
      | ~ v1_partfun1(B_300,A_299)
      | v1_xboole_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_578,plain,(
    ! [B_300] :
      ( v1_funct_1(k3_filter_1('#skF_6',B_300,'#skF_10'))
      | ~ v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1('#skF_10')
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2(B_300)
      | ~ v3_relat_2(B_300)
      | ~ v1_partfun1(B_300,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_186,c_576])).

tff(c_584,plain,(
    ! [B_300] :
      ( v1_funct_1(k3_filter_1('#skF_6',B_300,'#skF_10'))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2(B_300)
      | ~ v3_relat_2(B_300)
      | ~ v1_partfun1(B_300,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_143,c_578])).

tff(c_587,plain,(
    ! [B_302] :
      ( v1_funct_1(k3_filter_1('#skF_6',B_302,'#skF_10'))
      | ~ m1_subset_1(B_302,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2(B_302)
      | ~ v3_relat_2(B_302)
      | ~ v1_partfun1(B_302,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_584])).

tff(c_590,plain,
    ( v1_funct_1(k3_filter_1('#skF_6','#skF_7','#skF_10'))
    | ~ v8_relat_2('#skF_7')
    | ~ v3_relat_2('#skF_7')
    | ~ v1_partfun1('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_587])).

tff(c_597,plain,(
    v1_funct_1(k3_filter_1('#skF_6','#skF_7','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_590])).

tff(c_2403,plain,(
    ! [C_674,A_675] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_674),k11_relat_1('#skF_7','#skF_8'),A_675) = k11_relat_1('#skF_7',k1_binop_1(C_674,'#skF_8','#skF_5'(A_675)))
      | ~ r2_hidden(A_675,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_674))
      | ~ m2_filter_1(C_674,'#skF_6','#skF_7')
      | v1_xboole_0(A_675)
      | ~ m1_subset_1(C_674,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_674,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_674) ) ),
    inference(splitRight,[status(thm)],[c_2381])).

tff(c_2405,plain,(
    ! [A_675] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7','#skF_8'),A_675) = k11_relat_1('#skF_7',k1_binop_1('#skF_10','#skF_8','#skF_5'(A_675)))
      | ~ r2_hidden(A_675,k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7','#skF_10'))
      | ~ m2_filter_1('#skF_10','#skF_6','#skF_7')
      | v1_xboole_0(A_675)
      | ~ v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_186,c_2403])).

tff(c_2413,plain,(
    ! [A_676] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7','#skF_8'),A_676) = k11_relat_1('#skF_7',k1_binop_1('#skF_10','#skF_8','#skF_5'(A_676)))
      | ~ r2_hidden(A_676,k7_eqrel_1('#skF_6','#skF_7'))
      | v1_xboole_0(A_676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_143,c_62,c_597,c_2405])).

tff(c_450,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( k4_binop_1(A_287,B_288,C_289,D_290) = k1_binop_1(B_288,C_289,D_290)
      | ~ m1_subset_1(D_290,A_287)
      | ~ m1_subset_1(C_289,A_287)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_287,A_287),A_287)))
      | ~ v1_funct_2(B_288,k2_zfmisc_1(A_287,A_287),A_287)
      | ~ v1_funct_1(B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_500,plain,(
    ! [B_292,C_293] :
      ( k4_binop_1('#skF_6',B_292,C_293,'#skF_9') = k1_binop_1(B_292,C_293,'#skF_9')
      | ~ m1_subset_1(C_293,'#skF_6')
      | ~ m1_subset_1(B_292,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(B_292,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(B_292) ) ),
    inference(resolution,[status(thm)],[c_64,c_450])).

tff(c_599,plain,(
    ! [B_303] :
      ( k4_binop_1('#skF_6',B_303,'#skF_8','#skF_9') = k1_binop_1(B_303,'#skF_8','#skF_9')
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(B_303,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_66,c_500])).

tff(c_602,plain,
    ( k4_binop_1('#skF_6','#skF_10','#skF_8','#skF_9') = k1_binop_1('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_186,c_599])).

tff(c_609,plain,(
    k4_binop_1('#skF_6','#skF_10','#skF_8','#skF_9') = k1_binop_1('#skF_10','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_143,c_602])).

tff(c_60,plain,(
    k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k6_eqrel_1('#skF_6','#skF_6','#skF_7','#skF_8'),k6_eqrel_1('#skF_6','#skF_6','#skF_7','#skF_9')) != k6_eqrel_1('#skF_6','#skF_6','#skF_7',k4_binop_1('#skF_6','#skF_10','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_158,plain,(
    k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7','#skF_8'),k11_relat_1('#skF_7','#skF_9')) != k11_relat_1('#skF_7',k4_binop_1('#skF_6','#skF_10','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_155,c_155,c_60])).

tff(c_622,plain,(
    k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7','#skF_8'),k11_relat_1('#skF_7','#skF_9')) != k11_relat_1('#skF_7',k1_binop_1('#skF_10','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_158])).

tff(c_2422,plain,
    ( k11_relat_1('#skF_7',k1_binop_1('#skF_10','#skF_8','#skF_5'(k11_relat_1('#skF_7','#skF_9')))) != k11_relat_1('#skF_7',k1_binop_1('#skF_10','#skF_8','#skF_9'))
    | ~ r2_hidden(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7'))
    | v1_xboole_0(k11_relat_1('#skF_7','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2413,c_622])).

tff(c_2430,plain,(
    ~ r2_hidden(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2422])).

tff(c_2433,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_2430])).

tff(c_2436,plain,(
    v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_2433])).

tff(c_2438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_2436])).

tff(c_2440,plain,(
    r2_hidden(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2422])).

tff(c_1930,plain,(
    ! [C_584,G_581,C_583,A_582,B_580,E_579] :
      ( k6_eqrel_1(A_582,A_582,B_580,k1_binop_1(C_584,G_581,C_583)) = k1_binop_1(k3_filter_1(A_582,B_580,C_584),E_579,k11_relat_1('#skF_7',C_583))
      | ~ r2_hidden(G_581,E_579)
      | ~ r2_hidden(k11_relat_1('#skF_7',C_583),k8_eqrel_1(A_582,B_580))
      | ~ r2_hidden(E_579,k8_eqrel_1(A_582,B_580))
      | ~ m1_subset_1(k3_filter_1(A_582,B_580,C_584),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_582,B_580),k8_eqrel_1(A_582,B_580)),k8_eqrel_1(A_582,B_580))))
      | ~ v1_funct_2(k3_filter_1(A_582,B_580,C_584),k2_zfmisc_1(k8_eqrel_1(A_582,B_580),k8_eqrel_1(A_582,B_580)),k8_eqrel_1(A_582,B_580))
      | ~ v1_funct_1(k3_filter_1(A_582,B_580,C_584))
      | ~ m2_filter_1(C_584,A_582,B_580)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_582,A_582),A_582)))
      | ~ v1_funct_2(C_584,k2_zfmisc_1(A_582,A_582),A_582)
      | ~ v1_funct_1(C_584)
      | ~ m1_subset_1(B_580,k1_zfmisc_1(k2_zfmisc_1(A_582,A_582)))
      | ~ v8_relat_2(B_580)
      | ~ v3_relat_2(B_580)
      | ~ v1_partfun1(B_580,A_582)
      | v1_xboole_0(A_582)
      | ~ r2_hidden(C_583,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_283,c_1096])).

tff(c_4360,plain,(
    ! [C_927,C_930,A_926,C_929,B_928] :
      ( k6_eqrel_1(A_926,A_926,B_928,k1_binop_1(C_927,C_930,C_929)) = k1_binop_1(k3_filter_1(A_926,B_928,C_927),k11_relat_1('#skF_7',C_930),k11_relat_1('#skF_7',C_929))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_929),k8_eqrel_1(A_926,B_928))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_930),k8_eqrel_1(A_926,B_928))
      | ~ m1_subset_1(k3_filter_1(A_926,B_928,C_927),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_926,B_928),k8_eqrel_1(A_926,B_928)),k8_eqrel_1(A_926,B_928))))
      | ~ v1_funct_2(k3_filter_1(A_926,B_928,C_927),k2_zfmisc_1(k8_eqrel_1(A_926,B_928),k8_eqrel_1(A_926,B_928)),k8_eqrel_1(A_926,B_928))
      | ~ v1_funct_1(k3_filter_1(A_926,B_928,C_927))
      | ~ m2_filter_1(C_927,A_926,B_928)
      | ~ m1_subset_1(C_927,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_926,A_926),A_926)))
      | ~ v1_funct_2(C_927,k2_zfmisc_1(A_926,A_926),A_926)
      | ~ v1_funct_1(C_927)
      | ~ m1_subset_1(B_928,k1_zfmisc_1(k2_zfmisc_1(A_926,A_926)))
      | ~ v8_relat_2(B_928)
      | ~ v3_relat_2(B_928)
      | ~ v1_partfun1(B_928,A_926)
      | v1_xboole_0(A_926)
      | ~ r2_hidden(C_929,'#skF_6')
      | ~ r2_hidden(C_930,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_283,c_1930])).

tff(c_4364,plain,(
    ! [C_927,C_930,C_929] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_927),k11_relat_1('#skF_7',C_930),k11_relat_1('#skF_7',C_929)) = k6_eqrel_1('#skF_6','#skF_6','#skF_7',k1_binop_1(C_927,C_930,C_929))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_929),k8_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_930),k8_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_927),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_927),k2_zfmisc_1(k8_eqrel_1('#skF_6','#skF_7'),k8_eqrel_1('#skF_6','#skF_7')),k8_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_927))
      | ~ m2_filter_1(C_927,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_927,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_927,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_927)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v8_relat_2('#skF_7')
      | ~ v3_relat_2('#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_6')
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_929,'#skF_6')
      | ~ r2_hidden(C_930,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_4360])).

tff(c_4371,plain,(
    ! [C_927,C_930,C_929] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_927),k11_relat_1('#skF_7',C_930),k11_relat_1('#skF_7',C_929)) = k11_relat_1('#skF_7',k1_binop_1(C_927,C_930,C_929))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_929),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_930),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_927),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_927),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_927))
      | ~ m2_filter_1(C_927,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_927,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_927,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_927)
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden(C_929,'#skF_6')
      | ~ r2_hidden(C_930,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_253,c_253,c_253,c_253,c_253,c_253,c_253,c_155,c_4364])).

tff(c_4457,plain,(
    ! [C_936,C_937,C_938] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_936),k11_relat_1('#skF_7',C_937),k11_relat_1('#skF_7',C_938)) = k11_relat_1('#skF_7',k1_binop_1(C_936,C_937,C_938))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_938),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_937),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(k3_filter_1('#skF_6','#skF_7',C_936),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_936),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_936))
      | ~ m2_filter_1(C_936,'#skF_6','#skF_7')
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_936,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_936)
      | ~ r2_hidden(C_938,'#skF_6')
      | ~ r2_hidden(C_937,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4371])).

tff(c_4519,plain,(
    ! [C_940,C_941,C_942] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_940),k11_relat_1('#skF_7',C_941),k11_relat_1('#skF_7',C_942)) = k11_relat_1('#skF_7',k1_binop_1(C_940,C_941,C_942))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_942),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_941),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_2(k3_filter_1('#skF_6','#skF_7',C_940),k2_zfmisc_1(k7_eqrel_1('#skF_6','#skF_7'),k7_eqrel_1('#skF_6','#skF_7')),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_940))
      | ~ m2_filter_1(C_940,'#skF_6','#skF_7')
      | ~ r2_hidden(C_942,'#skF_6')
      | ~ r2_hidden(C_941,'#skF_6')
      | ~ m1_subset_1(C_940,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_940,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_940) ) ),
    inference(resolution,[status(thm)],[c_751,c_4457])).

tff(c_4523,plain,(
    ! [C_943,C_944,C_945] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7',C_943),k11_relat_1('#skF_7',C_944),k11_relat_1('#skF_7',C_945)) = k11_relat_1('#skF_7',k1_binop_1(C_943,C_944,C_945))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_945),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_944),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7',C_943))
      | ~ m2_filter_1(C_943,'#skF_6','#skF_7')
      | ~ r2_hidden(C_945,'#skF_6')
      | ~ r2_hidden(C_944,'#skF_6')
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')))
      | ~ v1_funct_2(C_943,k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1(C_943) ) ),
    inference(resolution,[status(thm)],[c_667,c_4519])).

tff(c_4525,plain,(
    ! [C_944,C_945] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7',C_944),k11_relat_1('#skF_7',C_945)) = k11_relat_1('#skF_7',k1_binop_1('#skF_10',C_944,C_945))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_945),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_944),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ v1_funct_1(k3_filter_1('#skF_6','#skF_7','#skF_10'))
      | ~ m2_filter_1('#skF_10','#skF_6','#skF_7')
      | ~ r2_hidden(C_945,'#skF_6')
      | ~ r2_hidden(C_944,'#skF_6')
      | ~ v1_funct_2('#skF_10',k2_zfmisc_1('#skF_6','#skF_6'),'#skF_6')
      | ~ v1_funct_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_186,c_4523])).

tff(c_4533,plain,(
    ! [C_946,C_947] :
      ( k1_binop_1(k3_filter_1('#skF_6','#skF_7','#skF_10'),k11_relat_1('#skF_7',C_946),k11_relat_1('#skF_7',C_947)) = k11_relat_1('#skF_7',k1_binop_1('#skF_10',C_946,C_947))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_947),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(k11_relat_1('#skF_7',C_946),k7_eqrel_1('#skF_6','#skF_7'))
      | ~ r2_hidden(C_947,'#skF_6')
      | ~ r2_hidden(C_946,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_143,c_62,c_597,c_4525])).

tff(c_4570,plain,
    ( ~ r2_hidden(k11_relat_1('#skF_7','#skF_9'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ r2_hidden(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7'))
    | ~ r2_hidden('#skF_9','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4533,c_622])).

tff(c_4643,plain,(
    ~ r2_hidden(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2393,c_2476,c_2440,c_4570])).

tff(c_4661,plain,
    ( v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
    | ~ m1_subset_1(k11_relat_1('#skF_7','#skF_8'),k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_56,c_4643])).

tff(c_4664,plain,(
    v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_4661])).

tff(c_4666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_4664])).

tff(c_4691,plain,(
    ! [A_952] : ~ r2_hidden(A_952,k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_4695,plain,(
    ! [A_184] :
      ( v1_xboole_0(k7_eqrel_1('#skF_6','#skF_7'))
      | ~ m1_subset_1(A_184,k7_eqrel_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_56,c_4691])).

tff(c_4699,plain,(
    ! [A_953] : ~ m1_subset_1(A_953,k7_eqrel_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_4695])).

tff(c_4704,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_40,c_4699])).

%------------------------------------------------------------------------------
