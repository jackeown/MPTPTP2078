%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1414+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 646 expanded)
%              Number of leaves         :   43 ( 252 expanded)
%              Depth                    :   19
%              Number of atoms          :  400 (2745 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > r2_hidden > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(f_214,negated_conjecture,(
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

tff(f_118,axiom,(
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

tff(f_169,axiom,(
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

tff(f_191,axiom,(
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

tff(f_85,axiom,(
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

tff(f_121,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_eqrel_1(B,A)
     => m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_134,axiom,(
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

tff(f_147,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_58,plain,(
    v1_partfun1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_56,plain,(
    v3_relat_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_54,plain,(
    v8_relat_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_50,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_48,plain,(
    m2_filter_1('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_63,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_88,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_funct_1(C_92)
      | ~ m2_filter_1(C_92,A_93,B_94)
      | ~ v1_relat_1(B_94)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_91,plain,
    ( v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_94,plain,
    ( v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_91])).

tff(c_95,plain,(
    v1_funct_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_94])).

tff(c_109,plain,(
    ! [C_103,A_104,B_105] :
      ( v1_funct_2(C_103,k2_zfmisc_1(A_104,A_104),A_104)
      | ~ m2_filter_1(C_103,A_104,B_105)
      | ~ v1_relat_1(B_105)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_111,plain,
    ( v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_114,plain,
    ( v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_111])).

tff(c_115,plain,(
    v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_114])).

tff(c_131,plain,(
    ! [C_112,A_113,B_114] :
      ( m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_113,A_113),A_113)))
      | ~ m2_filter_1(C_112,A_113,B_114)
      | ~ v1_relat_1(B_114)
      | v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_133,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_131])).

tff(c_136,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_133])).

tff(c_137,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_136])).

tff(c_46,plain,(
    r3_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_179,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_binop_1(A_122,B_123,C_124)
      | ~ r3_binop_1(A_122,B_123,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_122,A_122),A_122)))
      | ~ v1_funct_2(C_124,k2_zfmisc_1(A_122,A_122),A_122)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(B_123,A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_181,plain,
    ( r1_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_179])).

tff(c_184,plain,(
    r1_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_95,c_115,c_137,c_181])).

tff(c_40,plain,(
    ! [A_36,B_44,C_48,D_50] :
      ( r1_binop_1(k8_eqrel_1(A_36,B_44),k9_eqrel_1(A_36,B_44,C_48),k3_filter_1(A_36,B_44,D_50))
      | ~ r1_binop_1(A_36,C_48,D_50)
      | ~ m2_filter_1(D_50,A_36,B_44)
      | ~ m1_subset_1(C_48,A_36)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ v8_relat_2(B_44)
      | ~ v3_relat_2(B_44)
      | ~ v1_partfun1(B_44,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_185,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_binop_1(A_125,B_126,C_127)
      | ~ r3_binop_1(A_125,B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_125,A_125),A_125)))
      | ~ v1_funct_2(C_127,k2_zfmisc_1(A_125,A_125),A_125)
      | ~ v1_funct_1(C_127)
      | ~ m1_subset_1(B_126,A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_187,plain,
    ( r2_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')))
    | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_185])).

tff(c_190,plain,(
    r2_binop_1('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_95,c_115,c_137,c_187])).

tff(c_42,plain,(
    ! [A_51,B_59,C_63,D_65] :
      ( r2_binop_1(k8_eqrel_1(A_51,B_59),k9_eqrel_1(A_51,B_59,C_63),k3_filter_1(A_51,B_59,D_65))
      | ~ r2_binop_1(A_51,C_63,D_65)
      | ~ m2_filter_1(D_65,A_51,B_59)
      | ~ m1_subset_1(C_63,A_51)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_zfmisc_1(A_51,A_51)))
      | ~ v8_relat_2(B_59)
      | ~ v3_relat_2(B_59)
      | ~ v1_partfun1(B_59,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_149,plain,(
    ! [A_115,B_116] :
      ( m1_eqrel_1(k8_eqrel_1(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_115,A_115)))
      | ~ v1_partfun1(B_116,A_115)
      | ~ v8_relat_2(B_116)
      | ~ v3_relat_2(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_152,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_149])).

tff(c_159,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_58,c_152])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( ~ v1_xboole_0(B_3)
      | ~ m1_eqrel_1(B_3,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,
    ( ~ v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_166,plain,(
    ~ v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_163])).

tff(c_30,plain,(
    ! [A_25] : m1_subset_1('#skF_1'(A_25),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19)))
      | ~ m1_eqrel_1(B_20,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_191,plain,(
    ! [A_128,B_129,C_130] :
      ( m2_subset_1(k9_eqrel_1(A_128,B_129,C_130),k1_zfmisc_1(A_128),k8_eqrel_1(A_128,B_129))
      | ~ m1_subset_1(C_130,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(A_128,A_128)))
      | ~ v1_partfun1(B_129,A_128)
      | ~ v8_relat_2(B_129)
      | ~ v3_relat_2(B_129)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ! [C_30,B_28,A_27] :
      ( m1_subset_1(C_30,B_28)
      | ~ m2_subset_1(C_30,A_27,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27))
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_249,plain,(
    ! [A_152,B_153,C_154] :
      ( m1_subset_1(k9_eqrel_1(A_152,B_153,C_154),k8_eqrel_1(A_152,B_153))
      | ~ m1_subset_1(k8_eqrel_1(A_152,B_153),k1_zfmisc_1(k1_zfmisc_1(A_152)))
      | v1_xboole_0(k8_eqrel_1(A_152,B_153))
      | v1_xboole_0(k1_zfmisc_1(A_152))
      | ~ m1_subset_1(C_154,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1(A_152,A_152)))
      | ~ v1_partfun1(B_153,A_152)
      | ~ v8_relat_2(B_153)
      | ~ v3_relat_2(B_153)
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_191,c_32])).

tff(c_253,plain,(
    ! [A_19,B_153,C_154] :
      ( m1_subset_1(k9_eqrel_1(A_19,B_153,C_154),k8_eqrel_1(A_19,B_153))
      | v1_xboole_0(k8_eqrel_1(A_19,B_153))
      | v1_xboole_0(k1_zfmisc_1(A_19))
      | ~ m1_subset_1(C_154,A_19)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(k2_zfmisc_1(A_19,A_19)))
      | ~ v1_partfun1(B_153,A_19)
      | ~ v8_relat_2(B_153)
      | ~ v3_relat_2(B_153)
      | v1_xboole_0(A_19)
      | ~ m1_eqrel_1(k8_eqrel_1(A_19,B_153),A_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_222,plain,(
    ! [A_137,B_138,C_139] :
      ( v1_funct_1(k3_filter_1(A_137,B_138,C_139))
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_137,A_137),A_137)))
      | ~ v1_funct_2(C_139,k2_zfmisc_1(A_137,A_137),A_137)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1(A_137,A_137)))
      | ~ v8_relat_2(B_138)
      | ~ v3_relat_2(B_138)
      | ~ v1_partfun1(B_138,A_137)
      | v1_xboole_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_224,plain,(
    ! [B_138] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_138,'#skF_5'))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_138)
      | ~ v3_relat_2(B_138)
      | ~ v1_partfun1(B_138,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_137,c_222])).

tff(c_230,plain,(
    ! [B_138] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_138,'#skF_5'))
      | ~ m1_subset_1(B_138,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_138)
      | ~ v3_relat_2(B_138)
      | ~ v1_partfun1(B_138,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_115,c_224])).

tff(c_233,plain,(
    ! [B_140] :
      ( v1_funct_1(k3_filter_1('#skF_2',B_140,'#skF_5'))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_140)
      | ~ v3_relat_2(B_140)
      | ~ v1_partfun1(B_140,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_230])).

tff(c_236,plain,
    ( v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_233])).

tff(c_243,plain,(
    v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_236])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( v1_funct_2(k3_filter_1(A_11,B_12,C_13),k2_zfmisc_1(k8_eqrel_1(A_11,B_12),k8_eqrel_1(A_11,B_12)),k8_eqrel_1(A_11,B_12))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_11,A_11),A_11)))
      | ~ v1_funct_2(C_13,k2_zfmisc_1(A_11,A_11),A_11)
      | ~ v1_funct_1(C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k2_zfmisc_1(A_11,A_11)))
      | ~ v8_relat_2(B_12)
      | ~ v3_relat_2(B_12)
      | ~ v1_partfun1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_256,plain,(
    ! [A_160,B_161,C_162] :
      ( m1_subset_1(k3_filter_1(A_160,B_161,C_162),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_160,B_161),k8_eqrel_1(A_160,B_161)),k8_eqrel_1(A_160,B_161))))
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_160,A_160),A_160)))
      | ~ v1_funct_2(C_162,k2_zfmisc_1(A_160,A_160),A_160)
      | ~ v1_funct_1(C_162)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_zfmisc_1(A_160,A_160)))
      | ~ v8_relat_2(B_161)
      | ~ v3_relat_2(B_161)
      | ~ v1_partfun1(B_161,A_160)
      | v1_xboole_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

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

tff(c_306,plain,(
    ! [A_179,B_180,B_181,C_182] :
      ( r3_binop_1(k8_eqrel_1(A_179,B_180),B_181,k3_filter_1(A_179,B_180,C_182))
      | ~ r2_binop_1(k8_eqrel_1(A_179,B_180),B_181,k3_filter_1(A_179,B_180,C_182))
      | ~ r1_binop_1(k8_eqrel_1(A_179,B_180),B_181,k3_filter_1(A_179,B_180,C_182))
      | ~ v1_funct_2(k3_filter_1(A_179,B_180,C_182),k2_zfmisc_1(k8_eqrel_1(A_179,B_180),k8_eqrel_1(A_179,B_180)),k8_eqrel_1(A_179,B_180))
      | ~ v1_funct_1(k3_filter_1(A_179,B_180,C_182))
      | ~ m1_subset_1(B_181,k8_eqrel_1(A_179,B_180))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_179,A_179),A_179)))
      | ~ v1_funct_2(C_182,k2_zfmisc_1(A_179,A_179),A_179)
      | ~ v1_funct_1(C_182)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k2_zfmisc_1(A_179,A_179)))
      | ~ v8_relat_2(B_180)
      | ~ v3_relat_2(B_180)
      | ~ v1_partfun1(B_180,A_179)
      | v1_xboole_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_256,c_6])).

tff(c_310,plain,(
    ! [A_183,B_184,B_185,C_186] :
      ( r3_binop_1(k8_eqrel_1(A_183,B_184),B_185,k3_filter_1(A_183,B_184,C_186))
      | ~ r2_binop_1(k8_eqrel_1(A_183,B_184),B_185,k3_filter_1(A_183,B_184,C_186))
      | ~ r1_binop_1(k8_eqrel_1(A_183,B_184),B_185,k3_filter_1(A_183,B_184,C_186))
      | ~ v1_funct_1(k3_filter_1(A_183,B_184,C_186))
      | ~ m1_subset_1(B_185,k8_eqrel_1(A_183,B_184))
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_183,A_183),A_183)))
      | ~ v1_funct_2(C_186,k2_zfmisc_1(A_183,A_183),A_183)
      | ~ v1_funct_1(C_186)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1(A_183,A_183)))
      | ~ v8_relat_2(B_184)
      | ~ v3_relat_2(B_184)
      | ~ v1_partfun1(B_184,A_183)
      | v1_xboole_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_14,c_306])).

tff(c_314,plain,(
    ! [B_184,B_185] :
      ( r3_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ v1_funct_1(k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ m1_subset_1(B_185,k8_eqrel_1('#skF_2',B_184))
      | ~ v1_funct_2('#skF_5',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_184)
      | ~ v3_relat_2(B_184)
      | ~ v1_partfun1(B_184,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_137,c_310])).

tff(c_321,plain,(
    ! [B_184,B_185] :
      ( r3_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_2',B_184),B_185,k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ v1_funct_1(k3_filter_1('#skF_2',B_184,'#skF_5'))
      | ~ m1_subset_1(B_185,k8_eqrel_1('#skF_2',B_184))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_184)
      | ~ v3_relat_2(B_184)
      | ~ v1_partfun1(B_184,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_115,c_314])).

tff(c_324,plain,(
    ! [B_187,B_188] :
      ( r3_binop_1(k8_eqrel_1('#skF_2',B_187),B_188,k3_filter_1('#skF_2',B_187,'#skF_5'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_2',B_187),B_188,k3_filter_1('#skF_2',B_187,'#skF_5'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_2',B_187),B_188,k3_filter_1('#skF_2',B_187,'#skF_5'))
      | ~ v1_funct_1(k3_filter_1('#skF_2',B_187,'#skF_5'))
      | ~ m1_subset_1(B_188,k8_eqrel_1('#skF_2',B_187))
      | ~ m1_subset_1(B_187,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
      | ~ v8_relat_2(B_187)
      | ~ v3_relat_2(B_187)
      | ~ v1_partfun1(B_187,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_321])).

tff(c_44,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_331,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ v1_funct_1(k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k8_eqrel_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_324,c_44])).

tff(c_336,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k8_eqrel_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_243,c_331])).

tff(c_337,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k8_eqrel_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_344,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0(k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | v1_xboole_0('#skF_2')
    | ~ m1_eqrel_1(k8_eqrel_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_253,c_337])).

tff(c_347,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3'))
    | v1_xboole_0(k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_56,c_54,c_58,c_52,c_50,c_344])).

tff(c_348,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_166,c_347])).

tff(c_76,plain,(
    ! [C_89,B_90,A_91] :
      ( ~ v1_xboole_0(C_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(C_89))
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_84,plain,(
    ! [A_19,A_91,B_20] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_19))
      | ~ r2_hidden(A_91,B_20)
      | ~ m1_eqrel_1(B_20,A_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_352,plain,(
    ! [A_193,B_194] :
      ( ~ r2_hidden(A_193,B_194)
      | ~ m1_eqrel_1(B_194,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_348,c_84])).

tff(c_357,plain,(
    ! [B_195,A_196] :
      ( ~ m1_eqrel_1(B_195,'#skF_2')
      | v1_xboole_0(B_195)
      | ~ m1_subset_1(A_196,B_195) ) ),
    inference(resolution,[status(thm)],[c_36,c_352])).

tff(c_388,plain,(
    ! [A_197] :
      ( ~ m1_eqrel_1(A_197,'#skF_2')
      | v1_xboole_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_30,c_357])).

tff(c_395,plain,(
    v1_xboole_0(k8_eqrel_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_159,c_388])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_395])).

tff(c_401,plain,
    ( ~ r1_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5'))
    | ~ r2_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_403,plain,(
    ~ r2_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_406,plain,
    ( ~ r2_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m2_filter_1('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_403])).

tff(c_409,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_190,c_406])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_409])).

tff(c_412,plain,(
    ~ r1_binop_1(k8_eqrel_1('#skF_2','#skF_3'),k9_eqrel_1('#skF_2','#skF_3','#skF_4'),k3_filter_1('#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_420,plain,
    ( ~ r1_binop_1('#skF_2','#skF_4','#skF_5')
    | ~ m2_filter_1('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v8_relat_2('#skF_3')
    | ~ v3_relat_2('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_412])).

tff(c_423,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_184,c_420])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_423])).

%------------------------------------------------------------------------------
