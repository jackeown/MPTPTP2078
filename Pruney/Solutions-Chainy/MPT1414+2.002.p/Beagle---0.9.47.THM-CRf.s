%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:36 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 710 expanded)
%              Number of leaves         :   40 ( 272 expanded)
%              Depth                    :   18
%              Number of atoms          :  393 (2876 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_211,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(B) )
     => ! [C] :
          ( m2_filter_1(C,A,B)
         => ( v1_funct_1(C)
            & v1_funct_2(C,k2_zfmisc_1(A,A),A)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A,A),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_filter_1)).

tff(f_78,axiom,(
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

tff(f_166,axiom,(
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

tff(f_188,axiom,(
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

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => m1_eqrel_1(k8_eqrel_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_eqrel_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_eqrel_1(B,A)
         => ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_eqrel_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_eqrel_1(B,A)
     => m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_eqrel_1)).

tff(f_126,axiom,(
    ! [A,B,C] :
      ( ( ~ v1_xboole_0(A)
        & v3_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
        & m1_subset_1(C,A) )
     => m2_subset_1(k9_eqrel_1(A,B,C),k1_zfmisc_1(A),k8_eqrel_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_eqrel_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ! [C] :
          ( m2_subset_1(C,A,B)
        <=> m1_subset_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

tff(f_101,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_56,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_54,plain,(
    v3_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_52,plain,(
    v8_relat_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_48,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_46,plain,(
    m2_filter_1('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_62])).

tff(c_72,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_82,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_funct_1(C_85)
      | ~ m2_filter_1(C_85,A_86,B_87)
      | ~ v1_relat_1(B_87)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_85,plain,
    ( v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_88,plain,
    ( v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85])).

tff(c_89,plain,(
    v1_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_88])).

tff(c_91,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_funct_2(C_88,k2_zfmisc_1(A_89,A_89),A_89)
      | ~ m2_filter_1(C_88,A_89,B_90)
      | ~ v1_relat_1(B_90)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_93,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_96,plain,
    ( v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_93])).

tff(c_97,plain,(
    v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_96])).

tff(c_111,plain,(
    ! [C_101,A_102,B_103] :
      ( m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_102,A_102),A_102)))
      | ~ m2_filter_1(C_101,A_102,B_103)
      | ~ v1_relat_1(B_103)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_113,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_111])).

tff(c_116,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_113])).

tff(c_117,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_116])).

tff(c_44,plain,(
    r3_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_157,plain,(
    ! [A_112,B_113,C_114] :
      ( r1_binop_1(A_112,B_113,C_114)
      | ~ r3_binop_1(A_112,B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_112,A_112),A_112)))
      | ~ v1_funct_2(C_114,k2_zfmisc_1(A_112,A_112),A_112)
      | ~ v1_funct_1(C_114)
      | ~ m1_subset_1(B_113,A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_159,plain,
    ( r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_157])).

tff(c_162,plain,(
    r1_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_89,c_97,c_117,c_159])).

tff(c_38,plain,(
    ! [A_34,B_42,C_46,D_48] :
      ( r1_binop_1(k8_eqrel_1(A_34,B_42),k9_eqrel_1(A_34,B_42,C_46),k3_filter_1(A_34,B_42,D_48))
      | ~ r1_binop_1(A_34,C_46,D_48)
      | ~ m2_filter_1(D_48,A_34,B_42)
      | ~ m1_subset_1(C_46,A_34)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(A_34,A_34)))
      | ~ v8_relat_2(B_42)
      | ~ v3_relat_2(B_42)
      | ~ v1_partfun1(B_42,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_149,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_binop_1(A_109,B_110,C_111)
      | ~ r3_binop_1(A_109,B_110,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_109,A_109),A_109)))
      | ~ v1_funct_2(C_111,k2_zfmisc_1(A_109,A_109),A_109)
      | ~ v1_funct_1(C_111)
      | ~ m1_subset_1(B_110,A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,
    ( r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')))
    | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_149])).

tff(c_154,plain,(
    r2_binop_1('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_89,c_97,c_117,c_151])).

tff(c_40,plain,(
    ! [A_49,B_57,C_61,D_63] :
      ( r2_binop_1(k8_eqrel_1(A_49,B_57),k9_eqrel_1(A_49,B_57,C_61),k3_filter_1(A_49,B_57,D_63))
      | ~ r2_binop_1(A_49,C_61,D_63)
      | ~ m2_filter_1(D_63,A_49,B_57)
      | ~ m1_subset_1(C_61,A_49)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_zfmisc_1(A_49,A_49)))
      | ~ v8_relat_2(B_57)
      | ~ v3_relat_2(B_57)
      | ~ v1_partfun1(B_57,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_136,plain,(
    ! [A_107,B_108] :
      ( m1_eqrel_1(k8_eqrel_1(A_107,B_108),A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k2_zfmisc_1(A_107,A_107)))
      | ~ v1_partfun1(B_108,A_107)
      | ~ v8_relat_2(B_108)
      | ~ v3_relat_2(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_139,plain,
    ( m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_136])).

tff(c_142,plain,(
    m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_56,c_139])).

tff(c_12,plain,(
    ! [B_15,A_13] :
      ( ~ v1_xboole_0(B_15)
      | ~ m1_eqrel_1(B_15,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,
    ( ~ v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_142,c_12])).

tff(c_148,plain,(
    ~ v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_145])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28)))
      | ~ m1_eqrel_1(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_163,plain,(
    ! [A_115,B_116,C_117] :
      ( m2_subset_1(k9_eqrel_1(A_115,B_116,C_117),k1_zfmisc_1(A_115),k8_eqrel_1(A_115,B_116))
      | ~ m1_subset_1(C_117,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_115,A_115)))
      | ~ v1_partfun1(B_116,A_115)
      | ~ v8_relat_2(B_116)
      | ~ v3_relat_2(B_116)
      | v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [C_12,B_10,A_9] :
      ( m1_subset_1(C_12,B_10)
      | ~ m2_subset_1(C_12,A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9))
      | v1_xboole_0(B_10)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_200,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_subset_1(k9_eqrel_1(A_134,B_135,C_136),k8_eqrel_1(A_134,B_135))
      | ~ m1_subset_1(k8_eqrel_1(A_134,B_135),k1_zfmisc_1(k1_zfmisc_1(A_134)))
      | v1_xboole_0(k8_eqrel_1(A_134,B_135))
      | v1_xboole_0(k1_zfmisc_1(A_134))
      | ~ m1_subset_1(C_136,A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_134,A_134)))
      | ~ v1_partfun1(B_135,A_134)
      | ~ v8_relat_2(B_135)
      | ~ v3_relat_2(B_135)
      | v1_xboole_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_163,c_8])).

tff(c_204,plain,(
    ! [A_28,B_135,C_136] :
      ( m1_subset_1(k9_eqrel_1(A_28,B_135,C_136),k8_eqrel_1(A_28,B_135))
      | v1_xboole_0(k8_eqrel_1(A_28,B_135))
      | v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ m1_subset_1(C_136,A_28)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k2_zfmisc_1(A_28,A_28)))
      | ~ v1_partfun1(B_135,A_28)
      | ~ v8_relat_2(B_135)
      | ~ v3_relat_2(B_135)
      | v1_xboole_0(A_28)
      | ~ m1_eqrel_1(k8_eqrel_1(A_28,B_135),A_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_184,plain,(
    ! [A_122,B_123,C_124] :
      ( v1_funct_1(k3_filter_1(A_122,B_123,C_124))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_122,A_122),A_122)))
      | ~ v1_funct_2(C_124,k2_zfmisc_1(A_122,A_122),A_122)
      | ~ v1_funct_1(C_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1(A_122,A_122)))
      | ~ v8_relat_2(B_123)
      | ~ v3_relat_2(B_123)
      | ~ v1_partfun1(B_123,A_122)
      | v1_xboole_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_186,plain,(
    ! [B_123] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_123,'#skF_4'))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_123)
      | ~ v3_relat_2(B_123)
      | ~ v1_partfun1(B_123,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_117,c_184])).

tff(c_189,plain,(
    ! [B_123] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_123,'#skF_4'))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_123)
      | ~ v3_relat_2(B_123)
      | ~ v1_partfun1(B_123,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_97,c_186])).

tff(c_191,plain,(
    ! [B_125] :
      ( v1_funct_1(k3_filter_1('#skF_1',B_125,'#skF_4'))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_125)
      | ~ v3_relat_2(B_125)
      | ~ v1_partfun1(B_125,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_189])).

tff(c_194,plain,
    ( v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_191])).

tff(c_197,plain,(
    v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_194])).

tff(c_22,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_funct_2(k3_filter_1(A_20,B_21,C_22),k2_zfmisc_1(k8_eqrel_1(A_20,B_21),k8_eqrel_1(A_20,B_21)),k8_eqrel_1(A_20,B_21))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_20,A_20),A_20)))
      | ~ v1_funct_2(C_22,k2_zfmisc_1(A_20,A_20),A_20)
      | ~ v1_funct_1(C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k2_zfmisc_1(A_20,A_20)))
      | ~ v8_relat_2(B_21)
      | ~ v3_relat_2(B_21)
      | ~ v1_partfun1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_207,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1(k3_filter_1(A_143,B_144,C_145),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_143,B_144),k8_eqrel_1(A_143,B_144)),k8_eqrel_1(A_143,B_144))))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_143,A_143),A_143)))
      | ~ v1_funct_2(C_145,k2_zfmisc_1(A_143,A_143),A_143)
      | ~ v1_funct_1(C_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_zfmisc_1(A_143,A_143)))
      | ~ v8_relat_2(B_144)
      | ~ v3_relat_2(B_144)
      | ~ v1_partfun1(B_144,A_143)
      | v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_14,plain,(
    ! [A_16,B_17,C_19] :
      ( r3_binop_1(A_16,B_17,C_19)
      | ~ r2_binop_1(A_16,B_17,C_19)
      | ~ r1_binop_1(A_16,B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_16,A_16),A_16)))
      | ~ v1_funct_2(C_19,k2_zfmisc_1(A_16,A_16),A_16)
      | ~ v1_funct_1(C_19)
      | ~ m1_subset_1(B_17,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_249,plain,(
    ! [A_157,B_158,B_159,C_160] :
      ( r3_binop_1(k8_eqrel_1(A_157,B_158),B_159,k3_filter_1(A_157,B_158,C_160))
      | ~ r2_binop_1(k8_eqrel_1(A_157,B_158),B_159,k3_filter_1(A_157,B_158,C_160))
      | ~ r1_binop_1(k8_eqrel_1(A_157,B_158),B_159,k3_filter_1(A_157,B_158,C_160))
      | ~ v1_funct_2(k3_filter_1(A_157,B_158,C_160),k2_zfmisc_1(k8_eqrel_1(A_157,B_158),k8_eqrel_1(A_157,B_158)),k8_eqrel_1(A_157,B_158))
      | ~ v1_funct_1(k3_filter_1(A_157,B_158,C_160))
      | ~ m1_subset_1(B_159,k8_eqrel_1(A_157,B_158))
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_157,A_157),A_157)))
      | ~ v1_funct_2(C_160,k2_zfmisc_1(A_157,A_157),A_157)
      | ~ v1_funct_1(C_160)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v8_relat_2(B_158)
      | ~ v3_relat_2(B_158)
      | ~ v1_partfun1(B_158,A_157)
      | v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_207,c_14])).

tff(c_253,plain,(
    ! [A_161,B_162,B_163,C_164] :
      ( r3_binop_1(k8_eqrel_1(A_161,B_162),B_163,k3_filter_1(A_161,B_162,C_164))
      | ~ r2_binop_1(k8_eqrel_1(A_161,B_162),B_163,k3_filter_1(A_161,B_162,C_164))
      | ~ r1_binop_1(k8_eqrel_1(A_161,B_162),B_163,k3_filter_1(A_161,B_162,C_164))
      | ~ v1_funct_1(k3_filter_1(A_161,B_162,C_164))
      | ~ m1_subset_1(B_163,k8_eqrel_1(A_161,B_162))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_161,A_161),A_161)))
      | ~ v1_funct_2(C_164,k2_zfmisc_1(A_161,A_161),A_161)
      | ~ v1_funct_1(C_164)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1(A_161,A_161)))
      | ~ v8_relat_2(B_162)
      | ~ v3_relat_2(B_162)
      | ~ v1_partfun1(B_162,A_161)
      | v1_xboole_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_257,plain,(
    ! [B_162,B_163] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ m1_subset_1(B_163,k8_eqrel_1('#skF_1',B_162))
      | ~ v1_funct_2('#skF_4',k2_zfmisc_1('#skF_1','#skF_1'),'#skF_1')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_162)
      | ~ v3_relat_2(B_162)
      | ~ v1_partfun1(B_162,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_117,c_253])).

tff(c_261,plain,(
    ! [B_162,B_163] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_162),B_163,k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_162,'#skF_4'))
      | ~ m1_subset_1(B_163,k8_eqrel_1('#skF_1',B_162))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_162)
      | ~ v3_relat_2(B_162)
      | ~ v1_partfun1(B_162,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_97,c_257])).

tff(c_263,plain,(
    ! [B_165,B_166] :
      ( r3_binop_1(k8_eqrel_1('#skF_1',B_165),B_166,k3_filter_1('#skF_1',B_165,'#skF_4'))
      | ~ r2_binop_1(k8_eqrel_1('#skF_1',B_165),B_166,k3_filter_1('#skF_1',B_165,'#skF_4'))
      | ~ r1_binop_1(k8_eqrel_1('#skF_1',B_165),B_166,k3_filter_1('#skF_1',B_165,'#skF_4'))
      | ~ v1_funct_1(k3_filter_1('#skF_1',B_165,'#skF_4'))
      | ~ m1_subset_1(B_166,k8_eqrel_1('#skF_1',B_165))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ v8_relat_2(B_165)
      | ~ v3_relat_2(B_165)
      | ~ v1_partfun1(B_165,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_261])).

tff(c_42,plain,(
    ~ r3_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_270,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ v1_funct_1(k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_263,c_42])).

tff(c_275,plain,
    ( ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_197,c_270])).

tff(c_276,plain,(
    ~ m1_subset_1(k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_279,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | v1_xboole_0('#skF_1')
    | ~ m1_eqrel_1(k8_eqrel_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_204,c_276])).

tff(c_282,plain,
    ( v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2'))
    | v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_54,c_52,c_56,c_50,c_48,c_279])).

tff(c_283,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_148,c_282])).

tff(c_73,plain,(
    ! [B_83,A_84] :
      ( v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [B_29,A_28] :
      ( v1_xboole_0(B_29)
      | ~ v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ m1_eqrel_1(B_29,A_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_291,plain,(
    ! [B_171] :
      ( v1_xboole_0(B_171)
      | ~ m1_eqrel_1(B_171,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_283,c_80])).

tff(c_294,plain,(
    v1_xboole_0(k8_eqrel_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_142,c_291])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_294])).

tff(c_299,plain,
    ( ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4'))
    | ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_301,plain,(
    ~ r2_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_304,plain,
    ( ~ r2_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_301])).

tff(c_307,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_154,c_304])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_307])).

tff(c_310,plain,(
    ~ r1_binop_1(k8_eqrel_1('#skF_1','#skF_2'),k9_eqrel_1('#skF_1','#skF_2','#skF_3'),k3_filter_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_314,plain,
    ( ~ r1_binop_1('#skF_1','#skF_3','#skF_4')
    | ~ m2_filter_1('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v8_relat_2('#skF_2')
    | ~ v3_relat_2('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_310])).

tff(c_317,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_46,c_162,c_314])).

tff(c_319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.51  
% 3.05/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.51  %$ v1_funct_2 > r3_binop_1 > r2_binop_1 > r1_binop_1 > m2_subset_1 > m2_filter_1 > v1_partfun1 > m1_subset_1 > m1_eqrel_1 > v8_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_eqrel_1 > k3_filter_1 > k8_eqrel_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.05/1.51  
% 3.05/1.51  %Foreground sorts:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Background operators:
% 3.05/1.51  
% 3.05/1.51  
% 3.05/1.51  %Foreground operators:
% 3.05/1.51  tff(k8_eqrel_1, type, k8_eqrel_1: ($i * $i) > $i).
% 3.05/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.51  tff(m1_eqrel_1, type, m1_eqrel_1: ($i * $i) > $o).
% 3.05/1.51  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 3.05/1.51  tff(k9_eqrel_1, type, k9_eqrel_1: ($i * $i * $i) > $i).
% 3.05/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.05/1.51  tff(r3_binop_1, type, r3_binop_1: ($i * $i * $i) > $o).
% 3.05/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.51  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.05/1.51  tff(r1_binop_1, type, r1_binop_1: ($i * $i * $i) > $o).
% 3.05/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.05/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.51  tff(k3_filter_1, type, k3_filter_1: ($i * $i * $i) > $i).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.05/1.51  tff(m2_filter_1, type, m2_filter_1: ($i * $i * $i) > $o).
% 3.05/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.05/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.51  tff(m2_subset_1, type, m2_subset_1: ($i * $i * $i) > $o).
% 3.05/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.51  tff(r2_binop_1, type, r2_binop_1: ($i * $i * $i) > $o).
% 3.05/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.51  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 3.05/1.51  
% 3.05/1.53  tff(f_211, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r3_binop_1(A, C, D) => r3_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_filter_1)).
% 3.05/1.53  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.05/1.53  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.05/1.53  tff(f_144, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_relat_1(B)) => (![C]: (m2_filter_1(C, A, B) => ((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_filter_1)).
% 3.05/1.53  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => (r3_binop_1(A, B, C) <=> (r1_binop_1(A, B, C) & r2_binop_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_binop_1)).
% 3.05/1.53  tff(f_166, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r1_binop_1(A, C, D) => r1_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_filter_1)).
% 3.05/1.53  tff(f_188, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((((v1_partfun1(B, A) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (m1_subset_1(C, A) => (![D]: (m2_filter_1(D, A, B) => (r2_binop_1(A, C, D) => r2_binop_1(k8_eqrel_1(A, B), k9_eqrel_1(A, B, C), k3_filter_1(A, B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_filter_1)).
% 3.05/1.53  tff(f_111, axiom, (![A, B]: ((((v3_relat_2(B) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => m1_eqrel_1(k8_eqrel_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_eqrel_1)).
% 3.05/1.53  tff(f_63, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_eqrel_1(B, A) => ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_eqrel_1)).
% 3.05/1.53  tff(f_130, axiom, (![A, B]: (m1_eqrel_1(B, A) => m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_eqrel_1)).
% 3.05/1.53  tff(f_126, axiom, (![A, B, C]: ((((((~v1_xboole_0(A) & v3_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & m1_subset_1(C, A)) => m2_subset_1(k9_eqrel_1(A, B, C), k1_zfmisc_1(A), k8_eqrel_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_eqrel_1)).
% 3.05/1.53  tff(f_54, axiom, (![A, B]: (((~v1_xboole_0(A) & ~v1_xboole_0(B)) & m1_subset_1(B, k1_zfmisc_1(A))) => (![C]: (m2_subset_1(C, A, B) <=> m1_subset_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_m2_subset_1)).
% 3.05/1.53  tff(f_101, axiom, (![A, B, C]: ((((((((~v1_xboole_0(A) & v1_partfun1(B, A)) & v3_relat_2(B)) & v8_relat_2(B)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) & v1_funct_1(C)) & v1_funct_2(C, k2_zfmisc_1(A, A), A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A, A), A)))) => ((v1_funct_1(k3_filter_1(A, B, C)) & v1_funct_2(k3_filter_1(A, B, C), k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))) & m1_subset_1(k3_filter_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A, B), k8_eqrel_1(A, B)), k8_eqrel_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_filter_1)).
% 3.05/1.53  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.05/1.53  tff(c_58, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_56, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_54, plain, (v3_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_52, plain, (v8_relat_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_48, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_46, plain, (m2_filter_1('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.05/1.53  tff(c_62, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.05/1.53  tff(c_68, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_62])).
% 3.05/1.53  tff(c_72, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 3.05/1.53  tff(c_82, plain, (![C_85, A_86, B_87]: (v1_funct_1(C_85) | ~m2_filter_1(C_85, A_86, B_87) | ~v1_relat_1(B_87) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.05/1.53  tff(c_85, plain, (v1_funct_1('#skF_4') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_82])).
% 3.05/1.53  tff(c_88, plain, (v1_funct_1('#skF_4') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_85])).
% 3.05/1.53  tff(c_89, plain, (v1_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_88])).
% 3.05/1.53  tff(c_91, plain, (![C_88, A_89, B_90]: (v1_funct_2(C_88, k2_zfmisc_1(A_89, A_89), A_89) | ~m2_filter_1(C_88, A_89, B_90) | ~v1_relat_1(B_90) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.05/1.53  tff(c_93, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_91])).
% 3.05/1.53  tff(c_96, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_93])).
% 3.05/1.53  tff(c_97, plain, (v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_58, c_96])).
% 3.05/1.53  tff(c_111, plain, (![C_101, A_102, B_103]: (m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_102, A_102), A_102))) | ~m2_filter_1(C_101, A_102, B_103) | ~v1_relat_1(B_103) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.05/1.53  tff(c_113, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_111])).
% 3.05/1.53  tff(c_116, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_113])).
% 3.05/1.53  tff(c_117, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_58, c_116])).
% 3.05/1.53  tff(c_44, plain, (r3_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.05/1.53  tff(c_157, plain, (![A_112, B_113, C_114]: (r1_binop_1(A_112, B_113, C_114) | ~r3_binop_1(A_112, B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_112, A_112), A_112))) | ~v1_funct_2(C_114, k2_zfmisc_1(A_112, A_112), A_112) | ~v1_funct_1(C_114) | ~m1_subset_1(B_113, A_112))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.53  tff(c_159, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_157])).
% 3.05/1.53  tff(c_162, plain, (r1_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_89, c_97, c_117, c_159])).
% 3.05/1.53  tff(c_38, plain, (![A_34, B_42, C_46, D_48]: (r1_binop_1(k8_eqrel_1(A_34, B_42), k9_eqrel_1(A_34, B_42, C_46), k3_filter_1(A_34, B_42, D_48)) | ~r1_binop_1(A_34, C_46, D_48) | ~m2_filter_1(D_48, A_34, B_42) | ~m1_subset_1(C_46, A_34) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))) | ~v8_relat_2(B_42) | ~v3_relat_2(B_42) | ~v1_partfun1(B_42, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_166])).
% 3.05/1.53  tff(c_149, plain, (![A_109, B_110, C_111]: (r2_binop_1(A_109, B_110, C_111) | ~r3_binop_1(A_109, B_110, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_109, A_109), A_109))) | ~v1_funct_2(C_111, k2_zfmisc_1(A_109, A_109), A_109) | ~v1_funct_1(C_111) | ~m1_subset_1(B_110, A_109))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.53  tff(c_151, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1'))) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_149])).
% 3.05/1.53  tff(c_154, plain, (r2_binop_1('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_89, c_97, c_117, c_151])).
% 3.05/1.53  tff(c_40, plain, (![A_49, B_57, C_61, D_63]: (r2_binop_1(k8_eqrel_1(A_49, B_57), k9_eqrel_1(A_49, B_57, C_61), k3_filter_1(A_49, B_57, D_63)) | ~r2_binop_1(A_49, C_61, D_63) | ~m2_filter_1(D_63, A_49, B_57) | ~m1_subset_1(C_61, A_49) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))) | ~v8_relat_2(B_57) | ~v3_relat_2(B_57) | ~v1_partfun1(B_57, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.05/1.53  tff(c_136, plain, (![A_107, B_108]: (m1_eqrel_1(k8_eqrel_1(A_107, B_108), A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(k2_zfmisc_1(A_107, A_107))) | ~v1_partfun1(B_108, A_107) | ~v8_relat_2(B_108) | ~v3_relat_2(B_108))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.05/1.53  tff(c_139, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2')), inference(resolution, [status(thm)], [c_50, c_136])).
% 3.05/1.53  tff(c_142, plain, (m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_56, c_139])).
% 3.05/1.53  tff(c_12, plain, (![B_15, A_13]: (~v1_xboole_0(B_15) | ~m1_eqrel_1(B_15, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.05/1.53  tff(c_145, plain, (~v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_142, c_12])).
% 3.05/1.53  tff(c_148, plain, (~v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_145])).
% 3.05/1.53  tff(c_30, plain, (![B_29, A_28]: (m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))) | ~m1_eqrel_1(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.05/1.53  tff(c_163, plain, (![A_115, B_116, C_117]: (m2_subset_1(k9_eqrel_1(A_115, B_116, C_117), k1_zfmisc_1(A_115), k8_eqrel_1(A_115, B_116)) | ~m1_subset_1(C_117, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(k2_zfmisc_1(A_115, A_115))) | ~v1_partfun1(B_116, A_115) | ~v8_relat_2(B_116) | ~v3_relat_2(B_116) | v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.05/1.53  tff(c_8, plain, (![C_12, B_10, A_9]: (m1_subset_1(C_12, B_10) | ~m2_subset_1(C_12, A_9, B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)) | v1_xboole_0(B_10) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.53  tff(c_200, plain, (![A_134, B_135, C_136]: (m1_subset_1(k9_eqrel_1(A_134, B_135, C_136), k8_eqrel_1(A_134, B_135)) | ~m1_subset_1(k8_eqrel_1(A_134, B_135), k1_zfmisc_1(k1_zfmisc_1(A_134))) | v1_xboole_0(k8_eqrel_1(A_134, B_135)) | v1_xboole_0(k1_zfmisc_1(A_134)) | ~m1_subset_1(C_136, A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_134, A_134))) | ~v1_partfun1(B_135, A_134) | ~v8_relat_2(B_135) | ~v3_relat_2(B_135) | v1_xboole_0(A_134))), inference(resolution, [status(thm)], [c_163, c_8])).
% 3.05/1.53  tff(c_204, plain, (![A_28, B_135, C_136]: (m1_subset_1(k9_eqrel_1(A_28, B_135, C_136), k8_eqrel_1(A_28, B_135)) | v1_xboole_0(k8_eqrel_1(A_28, B_135)) | v1_xboole_0(k1_zfmisc_1(A_28)) | ~m1_subset_1(C_136, A_28) | ~m1_subset_1(B_135, k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))) | ~v1_partfun1(B_135, A_28) | ~v8_relat_2(B_135) | ~v3_relat_2(B_135) | v1_xboole_0(A_28) | ~m1_eqrel_1(k8_eqrel_1(A_28, B_135), A_28))), inference(resolution, [status(thm)], [c_30, c_200])).
% 3.05/1.53  tff(c_184, plain, (![A_122, B_123, C_124]: (v1_funct_1(k3_filter_1(A_122, B_123, C_124)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_122, A_122), A_122))) | ~v1_funct_2(C_124, k2_zfmisc_1(A_122, A_122), A_122) | ~v1_funct_1(C_124) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_zfmisc_1(A_122, A_122))) | ~v8_relat_2(B_123) | ~v3_relat_2(B_123) | ~v1_partfun1(B_123, A_122) | v1_xboole_0(A_122))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.05/1.53  tff(c_186, plain, (![B_123]: (v1_funct_1(k3_filter_1('#skF_1', B_123, '#skF_4')) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_123, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_123) | ~v3_relat_2(B_123) | ~v1_partfun1(B_123, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_184])).
% 3.05/1.53  tff(c_189, plain, (![B_123]: (v1_funct_1(k3_filter_1('#skF_1', B_123, '#skF_4')) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_123) | ~v3_relat_2(B_123) | ~v1_partfun1(B_123, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_97, c_186])).
% 3.05/1.53  tff(c_191, plain, (![B_125]: (v1_funct_1(k3_filter_1('#skF_1', B_125, '#skF_4')) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_125) | ~v3_relat_2(B_125) | ~v1_partfun1(B_125, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_189])).
% 3.05/1.53  tff(c_194, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_191])).
% 3.05/1.53  tff(c_197, plain, (v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_194])).
% 3.05/1.53  tff(c_22, plain, (![A_20, B_21, C_22]: (v1_funct_2(k3_filter_1(A_20, B_21, C_22), k2_zfmisc_1(k8_eqrel_1(A_20, B_21), k8_eqrel_1(A_20, B_21)), k8_eqrel_1(A_20, B_21)) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_20, A_20), A_20))) | ~v1_funct_2(C_22, k2_zfmisc_1(A_20, A_20), A_20) | ~v1_funct_1(C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(k2_zfmisc_1(A_20, A_20))) | ~v8_relat_2(B_21) | ~v3_relat_2(B_21) | ~v1_partfun1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.05/1.53  tff(c_207, plain, (![A_143, B_144, C_145]: (m1_subset_1(k3_filter_1(A_143, B_144, C_145), k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(A_143, B_144), k8_eqrel_1(A_143, B_144)), k8_eqrel_1(A_143, B_144)))) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_143, A_143), A_143))) | ~v1_funct_2(C_145, k2_zfmisc_1(A_143, A_143), A_143) | ~v1_funct_1(C_145) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_zfmisc_1(A_143, A_143))) | ~v8_relat_2(B_144) | ~v3_relat_2(B_144) | ~v1_partfun1(B_144, A_143) | v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.05/1.53  tff(c_14, plain, (![A_16, B_17, C_19]: (r3_binop_1(A_16, B_17, C_19) | ~r2_binop_1(A_16, B_17, C_19) | ~r1_binop_1(A_16, B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_16, A_16), A_16))) | ~v1_funct_2(C_19, k2_zfmisc_1(A_16, A_16), A_16) | ~v1_funct_1(C_19) | ~m1_subset_1(B_17, A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.53  tff(c_249, plain, (![A_157, B_158, B_159, C_160]: (r3_binop_1(k8_eqrel_1(A_157, B_158), B_159, k3_filter_1(A_157, B_158, C_160)) | ~r2_binop_1(k8_eqrel_1(A_157, B_158), B_159, k3_filter_1(A_157, B_158, C_160)) | ~r1_binop_1(k8_eqrel_1(A_157, B_158), B_159, k3_filter_1(A_157, B_158, C_160)) | ~v1_funct_2(k3_filter_1(A_157, B_158, C_160), k2_zfmisc_1(k8_eqrel_1(A_157, B_158), k8_eqrel_1(A_157, B_158)), k8_eqrel_1(A_157, B_158)) | ~v1_funct_1(k3_filter_1(A_157, B_158, C_160)) | ~m1_subset_1(B_159, k8_eqrel_1(A_157, B_158)) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_157, A_157), A_157))) | ~v1_funct_2(C_160, k2_zfmisc_1(A_157, A_157), A_157) | ~v1_funct_1(C_160) | ~m1_subset_1(B_158, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v8_relat_2(B_158) | ~v3_relat_2(B_158) | ~v1_partfun1(B_158, A_157) | v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_207, c_14])).
% 3.05/1.53  tff(c_253, plain, (![A_161, B_162, B_163, C_164]: (r3_binop_1(k8_eqrel_1(A_161, B_162), B_163, k3_filter_1(A_161, B_162, C_164)) | ~r2_binop_1(k8_eqrel_1(A_161, B_162), B_163, k3_filter_1(A_161, B_162, C_164)) | ~r1_binop_1(k8_eqrel_1(A_161, B_162), B_163, k3_filter_1(A_161, B_162, C_164)) | ~v1_funct_1(k3_filter_1(A_161, B_162, C_164)) | ~m1_subset_1(B_163, k8_eqrel_1(A_161, B_162)) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(A_161, A_161), A_161))) | ~v1_funct_2(C_164, k2_zfmisc_1(A_161, A_161), A_161) | ~v1_funct_1(C_164) | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1(A_161, A_161))) | ~v8_relat_2(B_162) | ~v3_relat_2(B_162) | ~v1_partfun1(B_162, A_161) | v1_xboole_0(A_161))), inference(resolution, [status(thm)], [c_22, c_249])).
% 3.27/1.53  tff(c_257, plain, (![B_162, B_163]: (r3_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_162, '#skF_4')) | ~m1_subset_1(B_163, k8_eqrel_1('#skF_1', B_162)) | ~v1_funct_2('#skF_4', k2_zfmisc_1('#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_162) | ~v3_relat_2(B_162) | ~v1_partfun1(B_162, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_253])).
% 3.27/1.53  tff(c_261, plain, (![B_162, B_163]: (r3_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_162), B_163, k3_filter_1('#skF_1', B_162, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_162, '#skF_4')) | ~m1_subset_1(B_163, k8_eqrel_1('#skF_1', B_162)) | ~m1_subset_1(B_162, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_162) | ~v3_relat_2(B_162) | ~v1_partfun1(B_162, '#skF_1') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_97, c_257])).
% 3.27/1.53  tff(c_263, plain, (![B_165, B_166]: (r3_binop_1(k8_eqrel_1('#skF_1', B_165), B_166, k3_filter_1('#skF_1', B_165, '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', B_165), B_166, k3_filter_1('#skF_1', B_165, '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', B_165), B_166, k3_filter_1('#skF_1', B_165, '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', B_165, '#skF_4')) | ~m1_subset_1(B_166, k8_eqrel_1('#skF_1', B_165)) | ~m1_subset_1(B_165, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2(B_165) | ~v3_relat_2(B_165) | ~v1_partfun1(B_165, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_261])).
% 3.27/1.53  tff(c_42, plain, (~r3_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_211])).
% 3.27/1.53  tff(c_270, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~v1_funct_1(k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_263, c_42])).
% 3.27/1.53  tff(c_275, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_197, c_270])).
% 3.27/1.53  tff(c_276, plain, (~m1_subset_1(k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k8_eqrel_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_275])).
% 3.27/1.53  tff(c_279, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_partfun1('#skF_2', '#skF_1') | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | v1_xboole_0('#skF_1') | ~m1_eqrel_1(k8_eqrel_1('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_204, c_276])).
% 3.27/1.53  tff(c_282, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2')) | v1_xboole_0(k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_54, c_52, c_56, c_50, c_48, c_279])).
% 3.27/1.53  tff(c_283, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_58, c_148, c_282])).
% 3.27/1.53  tff(c_73, plain, (![B_83, A_84]: (v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.53  tff(c_80, plain, (![B_29, A_28]: (v1_xboole_0(B_29) | ~v1_xboole_0(k1_zfmisc_1(A_28)) | ~m1_eqrel_1(B_29, A_28))), inference(resolution, [status(thm)], [c_30, c_73])).
% 3.27/1.53  tff(c_291, plain, (![B_171]: (v1_xboole_0(B_171) | ~m1_eqrel_1(B_171, '#skF_1'))), inference(resolution, [status(thm)], [c_283, c_80])).
% 3.27/1.53  tff(c_294, plain, (v1_xboole_0(k8_eqrel_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_291])).
% 3.27/1.53  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_294])).
% 3.27/1.53  tff(c_299, plain, (~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4')) | ~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_275])).
% 3.27/1.53  tff(c_301, plain, (~r2_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_299])).
% 3.27/1.53  tff(c_304, plain, (~r2_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_301])).
% 3.27/1.53  tff(c_307, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_154, c_304])).
% 3.27/1.53  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_307])).
% 3.27/1.53  tff(c_310, plain, (~r1_binop_1(k8_eqrel_1('#skF_1', '#skF_2'), k9_eqrel_1('#skF_1', '#skF_2', '#skF_3'), k3_filter_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_299])).
% 3.27/1.53  tff(c_314, plain, (~r1_binop_1('#skF_1', '#skF_3', '#skF_4') | ~m2_filter_1('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v8_relat_2('#skF_2') | ~v3_relat_2('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_310])).
% 3.27/1.53  tff(c_317, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_46, c_162, c_314])).
% 3.27/1.53  tff(c_319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_317])).
% 3.27/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.53  
% 3.27/1.53  Inference rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Ref     : 0
% 3.27/1.53  #Sup     : 45
% 3.27/1.53  #Fact    : 0
% 3.27/1.53  #Define  : 0
% 3.27/1.53  #Split   : 6
% 3.27/1.53  #Chain   : 0
% 3.27/1.53  #Close   : 0
% 3.27/1.53  
% 3.27/1.53  Ordering : KBO
% 3.27/1.53  
% 3.27/1.53  Simplification rules
% 3.27/1.53  ----------------------
% 3.27/1.53  #Subsume      : 1
% 3.27/1.53  #Demod        : 62
% 3.27/1.53  #Tautology    : 6
% 3.27/1.53  #SimpNegUnit  : 13
% 3.27/1.53  #BackRed      : 0
% 3.27/1.53  
% 3.27/1.53  #Partial instantiations: 0
% 3.27/1.53  #Strategies tried      : 1
% 3.27/1.53  
% 3.27/1.53  Timing (in seconds)
% 3.27/1.53  ----------------------
% 3.27/1.54  Preprocessing        : 0.34
% 3.27/1.54  Parsing              : 0.19
% 3.27/1.54  CNF conversion       : 0.03
% 3.27/1.54  Main loop            : 0.32
% 3.27/1.54  Inferencing          : 0.12
% 3.27/1.54  Reduction            : 0.09
% 3.27/1.54  Demodulation         : 0.06
% 3.27/1.54  BG Simplification    : 0.02
% 3.27/1.54  Subsumption          : 0.07
% 3.27/1.54  Abstraction          : 0.01
% 3.27/1.54  MUC search           : 0.00
% 3.27/1.54  Cooper               : 0.00
% 3.27/1.54  Total                : 0.71
% 3.27/1.54  Index Insertion      : 0.00
% 3.27/1.54  Index Deletion       : 0.00
% 3.27/1.54  Index Matching       : 0.00
% 3.27/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
