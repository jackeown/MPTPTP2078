%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:14 EST 2020

% Result     : Theorem 6.04s
% Output     : CNFRefutation 6.36s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 694 expanded)
%              Number of leaves         :   45 ( 263 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 (3109 expanded)
%              Number of equality atoms :   76 ( 366 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ~ v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_171,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_135,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( m1_subset_1(D,A)
                 => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_48,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_162,plain,(
    ! [C_122,A_123,B_124] :
      ( ~ v1_partfun1(C_122,A_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_xboole_0(B_124)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,
    ( ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_162])).

tff(c_173,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_168])).

tff(c_174,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_173])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_85,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_85])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [B_101,A_102] :
      ( v1_relat_1(B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_94])).

tff(c_104,plain,(
    ! [B_114,A_115] :
      ( k1_relat_1(B_114) = A_115
      | ~ v1_partfun1(B_114,A_115)
      | ~ v4_relat_1(B_114,A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_104])).

tff(c_113,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_48,c_107])).

tff(c_175,plain,(
    ! [B_125,A_126] :
      ( v1_funct_2(B_125,k1_relat_1(B_125),A_126)
      | ~ r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_178,plain,(
    ! [A_126] :
      ( v1_funct_2('#skF_5','#skF_1',A_126)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_126)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_175])).

tff(c_181,plain,(
    ! [A_127] :
      ( v1_funct_2('#skF_5','#skF_1',A_127)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_178])).

tff(c_185,plain,(
    ! [A_4] :
      ( v1_funct_2('#skF_5','#skF_1',A_4)
      | ~ v5_relat_1('#skF_5',A_4)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_188,plain,(
    ! [A_4] :
      ( v1_funct_2('#skF_5','#skF_1',A_4)
      | ~ v5_relat_1('#skF_5',A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_185])).

tff(c_283,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( m1_subset_1(k3_funct_2(A_136,B_137,C_138,D_139),B_137)
      | ~ m1_subset_1(D_139,A_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ v1_funct_2(C_138,A_136,B_137)
      | ~ v1_funct_1(C_138)
      | v1_xboole_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_291,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_139),'#skF_3')
      | ~ m1_subset_1(D_139,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_52,c_283])).

tff(c_303,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_139),'#skF_3')
      | ~ m1_subset_1(D_139,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_291])).

tff(c_304,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_1','#skF_3','#skF_5',D_139),'#skF_3')
      | ~ m1_subset_1(D_139,'#skF_1')
      | ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_303])).

tff(c_320,plain,(
    ~ v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_323,plain,(
    ~ v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_320])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_323])).

tff(c_329,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_50,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_341,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k3_funct_2(A_147,B_148,C_149,D_150) = k1_funct_1(C_149,D_150)
      | ~ m1_subset_1(D_150,A_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_2(C_149,A_147,B_148)
      | ~ v1_funct_1(C_149)
      | v1_xboole_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_355,plain,(
    ! [B_148,C_149] :
      ( k3_funct_2('#skF_2',B_148,C_149,'#skF_6') = k1_funct_1(C_149,'#skF_6')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_148)))
      | ~ v1_funct_2(C_149,'#skF_2',B_148)
      | ~ v1_funct_1(C_149)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_341])).

tff(c_480,plain,(
    ! [B_172,C_173] :
      ( k3_funct_2('#skF_2',B_172,C_173,'#skF_6') = k1_funct_1(C_173,'#skF_6')
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_172)))
      | ~ v1_funct_2(C_173,'#skF_2',B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_355])).

tff(c_483,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_480])).

tff(c_486,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_483])).

tff(c_289,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_139),'#skF_1')
      | ~ m1_subset_1(D_139,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_283])).

tff(c_299,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_139),'#skF_1')
      | ~ m1_subset_1(D_139,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_289])).

tff(c_300,plain,(
    ! [D_139] :
      ( m1_subset_1(k3_funct_2('#skF_2','#skF_1','#skF_4',D_139),'#skF_1')
      | ~ m1_subset_1(D_139,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_299])).

tff(c_491,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_300])).

tff(c_495,plain,(
    m1_subset_1(k1_funct_1('#skF_4','#skF_6'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_491])).

tff(c_34,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k3_funct_2(A_32,B_33,C_34,D_35) = k1_funct_1(C_34,D_35)
      | ~ m1_subset_1(D_35,A_32)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_498,plain,(
    ! [B_33,C_34] :
      ( k3_funct_2('#skF_1',B_33,C_34,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_34,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_33)))
      | ~ v1_funct_2(C_34,'#skF_1',B_33)
      | ~ v1_funct_1(C_34)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_495,c_34])).

tff(c_716,plain,(
    ! [B_195,C_196] :
      ( k3_funct_2('#skF_1',B_195,C_196,k1_funct_1('#skF_4','#skF_6')) = k1_funct_1(C_196,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_195)))
      | ~ v1_funct_2(C_196,'#skF_1',B_195)
      | ~ v1_funct_1(C_196) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_498])).

tff(c_726,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_716])).

tff(c_733,plain,(
    k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_329,c_726])).

tff(c_567,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k3_funct_2(A_178,B_179,C_180,D_181) = k7_partfun1(B_179,C_180,D_181)
      | ~ m1_subset_1(D_181,A_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_2(C_180,A_178,B_179)
      | ~ v1_funct_1(C_180)
      | v1_xboole_0(B_179)
      | v1_xboole_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_571,plain,(
    ! [B_179,C_180] :
      ( k3_funct_2('#skF_1',B_179,C_180,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_179,C_180,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_179)))
      | ~ v1_funct_2(C_180,'#skF_1',B_179)
      | ~ v1_funct_1(C_180)
      | v1_xboole_0(B_179)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_495,c_567])).

tff(c_957,plain,(
    ! [B_205,C_206] :
      ( k3_funct_2('#skF_1',B_205,C_206,k1_funct_1('#skF_4','#skF_6')) = k7_partfun1(B_205,C_206,k1_funct_1('#skF_4','#skF_6'))
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_205)))
      | ~ v1_funct_2(C_206,'#skF_1',B_205)
      | ~ v1_funct_1(C_206)
      | v1_xboole_0(B_205) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_571])).

tff(c_975,plain,
    ( k3_funct_2('#skF_1','#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_957])).

tff(c_984,plain,
    ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_329,c_733,c_975])).

tff(c_985,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_984])).

tff(c_46,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_487,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_46])).

tff(c_986,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_487])).

tff(c_447,plain,(
    ! [C_165,D_166,A_169,E_167,B_168] :
      ( v1_funct_1(k8_funct_2(A_169,B_168,C_165,D_166,E_167))
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(B_168,C_165)))
      | ~ v1_funct_1(E_167)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_169,B_168)))
      | ~ v1_funct_2(D_166,A_169,B_168)
      | ~ v1_funct_1(D_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_455,plain,(
    ! [A_169,D_166] :
      ( v1_funct_1(k8_funct_2(A_169,'#skF_1','#skF_3',D_166,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_169,'#skF_1')))
      | ~ v1_funct_2(D_166,A_169,'#skF_1')
      | ~ v1_funct_1(D_166) ) ),
    inference(resolution,[status(thm)],[c_52,c_447])).

tff(c_627,plain,(
    ! [A_184,D_185] :
      ( v1_funct_1(k8_funct_2(A_184,'#skF_1','#skF_3',D_185,'#skF_5'))
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_184,'#skF_1')))
      | ~ v1_funct_2(D_185,A_184,'#skF_1')
      | ~ v1_funct_1(D_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_455])).

tff(c_642,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_627])).

tff(c_650,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_642])).

tff(c_658,plain,(
    ! [E_188,A_190,B_189,D_187,C_186] :
      ( v1_funct_2(k8_funct_2(A_190,B_189,C_186,D_187,E_188),A_190,C_186)
      | ~ m1_subset_1(E_188,k1_zfmisc_1(k2_zfmisc_1(B_189,C_186)))
      | ~ v1_funct_1(E_188)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189)))
      | ~ v1_funct_2(D_187,A_190,B_189)
      | ~ v1_funct_1(D_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_669,plain,(
    ! [A_190,D_187] :
      ( v1_funct_2(k8_funct_2(A_190,'#skF_1','#skF_3',D_187,'#skF_5'),A_190,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(A_190,'#skF_1')))
      | ~ v1_funct_2(D_187,A_190,'#skF_1')
      | ~ v1_funct_1(D_187) ) ),
    inference(resolution,[status(thm)],[c_52,c_658])).

tff(c_696,plain,(
    ! [A_193,D_194] :
      ( v1_funct_2(k8_funct_2(A_193,'#skF_1','#skF_3',D_194,'#skF_5'),A_193,'#skF_3')
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_193,'#skF_1')))
      | ~ v1_funct_2(D_194,A_193,'#skF_1')
      | ~ v1_funct_1(D_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_669])).

tff(c_707,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_696])).

tff(c_715,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_707])).

tff(c_69,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_92,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_85])).

tff(c_145,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_1002,plain,(
    ! [E_216,D_211,C_214,B_213,F_215,A_212] :
      ( k7_partfun1(A_212,E_216,k1_funct_1(D_211,F_215)) = k1_funct_1(k8_funct_2(B_213,C_214,A_212,D_211,E_216),F_215)
      | k1_xboole_0 = B_213
      | ~ r1_tarski(k2_relset_1(B_213,C_214,D_211),k1_relset_1(C_214,A_212,E_216))
      | ~ m1_subset_1(F_215,B_213)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(C_214,A_212)))
      | ~ v1_funct_1(E_216)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(B_213,C_214)))
      | ~ v1_funct_2(D_211,B_213,C_214)
      | ~ v1_funct_1(D_211)
      | v1_xboole_0(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1010,plain,(
    ! [A_212,E_216,F_215] :
      ( k7_partfun1(A_212,E_216,k1_funct_1('#skF_4',F_215)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_212,'#skF_4',E_216),F_215)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_212,E_216))
      | ~ m1_subset_1(F_215,'#skF_2')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_212)))
      | ~ v1_funct_1(E_216)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1002])).

tff(c_1019,plain,(
    ! [A_212,E_216,F_215] :
      ( k7_partfun1(A_212,E_216,k1_funct_1('#skF_4',F_215)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_212,'#skF_4',E_216),F_215)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_212,E_216))
      | ~ m1_subset_1(F_215,'#skF_2')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_212)))
      | ~ v1_funct_1(E_216)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1010])).

tff(c_1020,plain,(
    ! [A_212,E_216,F_215] :
      ( k7_partfun1(A_212,E_216,k1_funct_1('#skF_4',F_215)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_212,'#skF_4',E_216),F_215)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_212,E_216))
      | ~ m1_subset_1(F_215,'#skF_2')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_212)))
      | ~ v1_funct_1(E_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1019])).

tff(c_1409,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1020])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1411,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_2])).

tff(c_1413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1411])).

tff(c_1415,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1020])).

tff(c_117,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_117])).

tff(c_139,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_125])).

tff(c_1012,plain,(
    ! [D_211,F_215,B_213] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_211,F_215)) = k1_funct_1(k8_funct_2(B_213,'#skF_1','#skF_3',D_211,'#skF_5'),F_215)
      | k1_xboole_0 = B_213
      | ~ r1_tarski(k2_relset_1(B_213,'#skF_1',D_211),'#skF_1')
      | ~ m1_subset_1(F_215,B_213)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(B_213,'#skF_1')))
      | ~ v1_funct_2(D_211,B_213,'#skF_1')
      | ~ v1_funct_1(D_211)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_1002])).

tff(c_1022,plain,(
    ! [D_211,F_215,B_213] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_211,F_215)) = k1_funct_1(k8_funct_2(B_213,'#skF_1','#skF_3',D_211,'#skF_5'),F_215)
      | k1_xboole_0 = B_213
      | ~ r1_tarski(k2_relset_1(B_213,'#skF_1',D_211),'#skF_1')
      | ~ m1_subset_1(F_215,B_213)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(B_213,'#skF_1')))
      | ~ v1_funct_2(D_211,B_213,'#skF_1')
      | ~ v1_funct_1(D_211)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1012])).

tff(c_2212,plain,(
    ! [D_317,F_318,B_319] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_317,F_318)) = k1_funct_1(k8_funct_2(B_319,'#skF_1','#skF_3',D_317,'#skF_5'),F_318)
      | k1_xboole_0 = B_319
      | ~ r1_tarski(k2_relset_1(B_319,'#skF_1',D_317),'#skF_1')
      | ~ m1_subset_1(F_318,B_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(B_319,'#skF_1')))
      | ~ v1_funct_2(D_317,B_319,'#skF_1')
      | ~ v1_funct_1(D_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1022])).

tff(c_2235,plain,(
    ! [F_318] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_318)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_318)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_318,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_2212])).

tff(c_2247,plain,(
    ! [F_318] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_318)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_318)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_318,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_152,c_2235])).

tff(c_2248,plain,(
    ! [F_318] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_318)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_318)
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_318,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1415,c_2247])).

tff(c_2250,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2248])).

tff(c_2253,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_2250])).

tff(c_2257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_92,c_2253])).

tff(c_2364,plain,(
    ! [F_326] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_326)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_326)
      | ~ m1_subset_1(F_326,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2248])).

tff(c_2374,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2364,c_985])).

tff(c_2386,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2374])).

tff(c_28,plain,(
    ! [C_29,D_30,B_28,A_27,E_31] :
      ( m1_subset_1(k8_funct_2(A_27,B_28,C_29,D_30,E_31),k1_zfmisc_1(k2_zfmisc_1(A_27,C_29)))
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(B_28,C_29)))
      | ~ v1_funct_1(E_31)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_2(D_30,A_27,B_28)
      | ~ v1_funct_1(D_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_767,plain,(
    ! [A_202,D_199,E_200,C_198,B_201] :
      ( m1_subset_1(k8_funct_2(A_202,B_201,C_198,D_199,E_200),k1_zfmisc_1(k2_zfmisc_1(A_202,C_198)))
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(B_201,C_198)))
      | ~ v1_funct_1(E_200)
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201)))
      | ~ v1_funct_2(D_199,A_202,B_201)
      | ~ v1_funct_1(D_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2306,plain,(
    ! [C_323,D_324,A_325,B_321,E_322] :
      ( k1_relset_1(A_325,C_323,k8_funct_2(A_325,B_321,C_323,D_324,E_322)) = k1_relat_1(k8_funct_2(A_325,B_321,C_323,D_324,E_322))
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(B_321,C_323)))
      | ~ v1_funct_1(E_322)
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_325,B_321)))
      | ~ v1_funct_2(D_324,A_325,B_321)
      | ~ v1_funct_1(D_324) ) ),
    inference(resolution,[status(thm)],[c_767,c_16])).

tff(c_2328,plain,(
    ! [A_325,D_324] :
      ( k1_relset_1(A_325,'#skF_3',k8_funct_2(A_325,'#skF_1','#skF_3',D_324,'#skF_5')) = k1_relat_1(k8_funct_2(A_325,'#skF_1','#skF_3',D_324,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_324,k1_zfmisc_1(k2_zfmisc_1(A_325,'#skF_1')))
      | ~ v1_funct_2(D_324,A_325,'#skF_1')
      | ~ v1_funct_1(D_324) ) ),
    inference(resolution,[status(thm)],[c_52,c_2306])).

tff(c_2634,plain,(
    ! [A_360,D_361] :
      ( k1_relset_1(A_360,'#skF_3',k8_funct_2(A_360,'#skF_1','#skF_3',D_361,'#skF_5')) = k1_relat_1(k8_funct_2(A_360,'#skF_1','#skF_3',D_361,'#skF_5'))
      | ~ m1_subset_1(D_361,k1_zfmisc_1(k2_zfmisc_1(A_360,'#skF_1')))
      | ~ v1_funct_2(D_361,A_360,'#skF_1')
      | ~ v1_funct_1(D_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2328])).

tff(c_2657,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_2634])).

tff(c_2669,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2657])).

tff(c_38,plain,(
    ! [B_52,F_67,E_65,D_61,C_53,A_51] :
      ( k7_partfun1(A_51,E_65,k1_funct_1(D_61,F_67)) = k1_funct_1(k8_funct_2(B_52,C_53,A_51,D_61,E_65),F_67)
      | k1_xboole_0 = B_52
      | ~ r1_tarski(k2_relset_1(B_52,C_53,D_61),k1_relset_1(C_53,A_51,E_65))
      | ~ m1_subset_1(F_67,B_52)
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(C_53,A_51)))
      | ~ v1_funct_1(E_65)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_52,C_53)))
      | ~ v1_funct_2(D_61,B_52,C_53)
      | ~ v1_funct_1(D_61)
      | v1_xboole_0(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2672,plain,(
    ! [D_61,F_67,B_52] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_61,F_67)) = k1_funct_1(k8_funct_2(B_52,'#skF_2','#skF_3',D_61,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_67)
      | k1_xboole_0 = B_52
      | ~ r1_tarski(k2_relset_1(B_52,'#skF_2',D_61),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_67,B_52)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_52,'#skF_2')))
      | ~ v1_funct_2(D_61,B_52,'#skF_2')
      | ~ v1_funct_1(D_61)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2669,c_38])).

tff(c_2676,plain,(
    ! [D_61,F_67,B_52] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_61,F_67)) = k1_funct_1(k8_funct_2(B_52,'#skF_2','#skF_3',D_61,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_67)
      | k1_xboole_0 = B_52
      | ~ r1_tarski(k2_relset_1(B_52,'#skF_2',D_61),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_67,B_52)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_52,'#skF_2')))
      | ~ v1_funct_2(D_61,B_52,'#skF_2')
      | ~ v1_funct_1(D_61)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_2672])).

tff(c_2677,plain,(
    ! [D_61,F_67,B_52] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_61,F_67)) = k1_funct_1(k8_funct_2(B_52,'#skF_2','#skF_3',D_61,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_67)
      | k1_xboole_0 = B_52
      | ~ r1_tarski(k2_relset_1(B_52,'#skF_2',D_61),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_67,B_52)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_52,'#skF_2')))
      | ~ v1_funct_2(D_61,B_52,'#skF_2')
      | ~ v1_funct_1(D_61) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2676])).

tff(c_2771,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2677])).

tff(c_2774,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2771])).

tff(c_2778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_2774])).

tff(c_2780,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2677])).

tff(c_368,plain,(
    ! [B_148,C_149] :
      ( k3_funct_2('#skF_2',B_148,C_149,'#skF_6') = k1_funct_1(C_149,'#skF_6')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_148)))
      | ~ v1_funct_2(C_149,'#skF_2',B_148)
      | ~ v1_funct_1(C_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_355])).

tff(c_2800,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2780,c_368])).

tff(c_2850,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_715,c_2386,c_2800])).

tff(c_2852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_986,c_2850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:32:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.04/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.17  
% 6.04/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.04/2.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.04/2.18  
% 6.04/2.18  %Foreground sorts:
% 6.04/2.18  
% 6.04/2.18  
% 6.04/2.18  %Background operators:
% 6.04/2.18  
% 6.04/2.18  
% 6.04/2.18  %Foreground operators:
% 6.04/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.04/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.04/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.04/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.04/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.04/2.18  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.04/2.18  tff('#skF_5', type, '#skF_5': $i).
% 6.04/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.04/2.18  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.04/2.18  tff('#skF_6', type, '#skF_6': $i).
% 6.04/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.04/2.18  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.04/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.04/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.04/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.04/2.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.04/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.04/2.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.04/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.04/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.04/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.04/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.04/2.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.04/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.04/2.18  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.04/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.04/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.04/2.18  
% 6.36/2.22  tff(f_198, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k7_partfun1(C, E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_funct_2)).
% 6.36/2.22  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_partfun1)).
% 6.36/2.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.36/2.22  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.36/2.22  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.36/2.22  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.36/2.22  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 6.36/2.22  tff(f_171, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.36/2.22  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 6.36/2.22  tff(f_116, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.36/2.22  tff(f_135, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_2)).
% 6.36/2.22  tff(f_103, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 6.36/2.22  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.36/2.22  tff(f_159, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 6.36/2.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.36/2.22  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.36/2.22  tff(c_64, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_48, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_162, plain, (![C_122, A_123, B_124]: (~v1_partfun1(C_122, A_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_xboole_0(B_124) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.36/2.22  tff(c_168, plain, (~v1_partfun1('#skF_5', '#skF_1') | ~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_162])).
% 6.36/2.22  tff(c_173, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_168])).
% 6.36/2.22  tff(c_174, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_173])).
% 6.36/2.22  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_85, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.36/2.22  tff(c_93, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_85])).
% 6.36/2.22  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.36/2.22  tff(c_66, plain, (![B_101, A_102]: (v1_relat_1(B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.36/2.22  tff(c_72, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_66])).
% 6.36/2.22  tff(c_78, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 6.36/2.22  tff(c_8, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.36/2.22  tff(c_94, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.36/2.22  tff(c_102, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_94])).
% 6.36/2.22  tff(c_104, plain, (![B_114, A_115]: (k1_relat_1(B_114)=A_115 | ~v1_partfun1(B_114, A_115) | ~v4_relat_1(B_114, A_115) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.36/2.22  tff(c_107, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_102, c_104])).
% 6.36/2.22  tff(c_113, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_48, c_107])).
% 6.36/2.22  tff(c_175, plain, (![B_125, A_126]: (v1_funct_2(B_125, k1_relat_1(B_125), A_126) | ~r1_tarski(k2_relat_1(B_125), A_126) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.36/2.22  tff(c_178, plain, (![A_126]: (v1_funct_2('#skF_5', '#skF_1', A_126) | ~r1_tarski(k2_relat_1('#skF_5'), A_126) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_175])).
% 6.36/2.22  tff(c_181, plain, (![A_127]: (v1_funct_2('#skF_5', '#skF_1', A_127) | ~r1_tarski(k2_relat_1('#skF_5'), A_127))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_178])).
% 6.36/2.22  tff(c_185, plain, (![A_4]: (v1_funct_2('#skF_5', '#skF_1', A_4) | ~v5_relat_1('#skF_5', A_4) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_8, c_181])).
% 6.36/2.22  tff(c_188, plain, (![A_4]: (v1_funct_2('#skF_5', '#skF_1', A_4) | ~v5_relat_1('#skF_5', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_185])).
% 6.36/2.22  tff(c_283, plain, (![A_136, B_137, C_138, D_139]: (m1_subset_1(k3_funct_2(A_136, B_137, C_138, D_139), B_137) | ~m1_subset_1(D_139, A_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~v1_funct_2(C_138, A_136, B_137) | ~v1_funct_1(C_138) | v1_xboole_0(A_136))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.36/2.22  tff(c_291, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_139), '#skF_3') | ~m1_subset_1(D_139, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_52, c_283])).
% 6.36/2.22  tff(c_303, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_139), '#skF_3') | ~m1_subset_1(D_139, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_291])).
% 6.36/2.22  tff(c_304, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_1', '#skF_3', '#skF_5', D_139), '#skF_3') | ~m1_subset_1(D_139, '#skF_1') | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_303])).
% 6.36/2.22  tff(c_320, plain, (~v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_304])).
% 6.36/2.22  tff(c_323, plain, (~v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_188, c_320])).
% 6.36/2.22  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_323])).
% 6.36/2.22  tff(c_329, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_304])).
% 6.36/2.22  tff(c_50, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_341, plain, (![A_147, B_148, C_149, D_150]: (k3_funct_2(A_147, B_148, C_149, D_150)=k1_funct_1(C_149, D_150) | ~m1_subset_1(D_150, A_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_2(C_149, A_147, B_148) | ~v1_funct_1(C_149) | v1_xboole_0(A_147))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.36/2.22  tff(c_355, plain, (![B_148, C_149]: (k3_funct_2('#skF_2', B_148, C_149, '#skF_6')=k1_funct_1(C_149, '#skF_6') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_148))) | ~v1_funct_2(C_149, '#skF_2', B_148) | ~v1_funct_1(C_149) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_341])).
% 6.36/2.22  tff(c_480, plain, (![B_172, C_173]: (k3_funct_2('#skF_2', B_172, C_173, '#skF_6')=k1_funct_1(C_173, '#skF_6') | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_172))) | ~v1_funct_2(C_173, '#skF_2', B_172) | ~v1_funct_1(C_173))), inference(negUnitSimplification, [status(thm)], [c_62, c_355])).
% 6.36/2.22  tff(c_483, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_480])).
% 6.36/2.22  tff(c_486, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_483])).
% 6.36/2.22  tff(c_289, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_139), '#skF_1') | ~m1_subset_1(D_139, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_283])).
% 6.36/2.22  tff(c_299, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_139), '#skF_1') | ~m1_subset_1(D_139, '#skF_2') | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_289])).
% 6.36/2.22  tff(c_300, plain, (![D_139]: (m1_subset_1(k3_funct_2('#skF_2', '#skF_1', '#skF_4', D_139), '#skF_1') | ~m1_subset_1(D_139, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_299])).
% 6.36/2.22  tff(c_491, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_486, c_300])).
% 6.36/2.22  tff(c_495, plain, (m1_subset_1(k1_funct_1('#skF_4', '#skF_6'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_491])).
% 6.36/2.22  tff(c_34, plain, (![A_32, B_33, C_34, D_35]: (k3_funct_2(A_32, B_33, C_34, D_35)=k1_funct_1(C_34, D_35) | ~m1_subset_1(D_35, A_32) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.36/2.22  tff(c_498, plain, (![B_33, C_34]: (k3_funct_2('#skF_1', B_33, C_34, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_34, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_33))) | ~v1_funct_2(C_34, '#skF_1', B_33) | ~v1_funct_1(C_34) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_495, c_34])).
% 6.36/2.22  tff(c_716, plain, (![B_195, C_196]: (k3_funct_2('#skF_1', B_195, C_196, k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1(C_196, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_195))) | ~v1_funct_2(C_196, '#skF_1', B_195) | ~v1_funct_1(C_196))), inference(negUnitSimplification, [status(thm)], [c_64, c_498])).
% 6.36/2.22  tff(c_726, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_716])).
% 6.36/2.22  tff(c_733, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_329, c_726])).
% 6.36/2.22  tff(c_567, plain, (![A_178, B_179, C_180, D_181]: (k3_funct_2(A_178, B_179, C_180, D_181)=k7_partfun1(B_179, C_180, D_181) | ~m1_subset_1(D_181, A_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_2(C_180, A_178, B_179) | ~v1_funct_1(C_180) | v1_xboole_0(B_179) | v1_xboole_0(A_178))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.36/2.22  tff(c_571, plain, (![B_179, C_180]: (k3_funct_2('#skF_1', B_179, C_180, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_179, C_180, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_179))) | ~v1_funct_2(C_180, '#skF_1', B_179) | ~v1_funct_1(C_180) | v1_xboole_0(B_179) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_495, c_567])).
% 6.36/2.22  tff(c_957, plain, (![B_205, C_206]: (k3_funct_2('#skF_1', B_205, C_206, k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1(B_205, C_206, k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_205))) | ~v1_funct_2(C_206, '#skF_1', B_205) | ~v1_funct_1(C_206) | v1_xboole_0(B_205))), inference(negUnitSimplification, [status(thm)], [c_64, c_571])).
% 6.36/2.22  tff(c_975, plain, (k3_funct_2('#skF_1', '#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v1_funct_2('#skF_5', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_957])).
% 6.36/2.22  tff(c_984, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_329, c_733, c_975])).
% 6.36/2.22  tff(c_985, plain, (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_174, c_984])).
% 6.36/2.22  tff(c_46, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 6.36/2.22  tff(c_487, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_46])).
% 6.36/2.22  tff(c_986, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_487])).
% 6.36/2.22  tff(c_447, plain, (![C_165, D_166, A_169, E_167, B_168]: (v1_funct_1(k8_funct_2(A_169, B_168, C_165, D_166, E_167)) | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(B_168, C_165))) | ~v1_funct_1(E_167) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_169, B_168))) | ~v1_funct_2(D_166, A_169, B_168) | ~v1_funct_1(D_166))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.36/2.22  tff(c_455, plain, (![A_169, D_166]: (v1_funct_1(k8_funct_2(A_169, '#skF_1', '#skF_3', D_166, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_169, '#skF_1'))) | ~v1_funct_2(D_166, A_169, '#skF_1') | ~v1_funct_1(D_166))), inference(resolution, [status(thm)], [c_52, c_447])).
% 6.36/2.22  tff(c_627, plain, (![A_184, D_185]: (v1_funct_1(k8_funct_2(A_184, '#skF_1', '#skF_3', D_185, '#skF_5')) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_184, '#skF_1'))) | ~v1_funct_2(D_185, A_184, '#skF_1') | ~v1_funct_1(D_185))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_455])).
% 6.36/2.22  tff(c_642, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_627])).
% 6.36/2.22  tff(c_650, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_642])).
% 6.36/2.22  tff(c_658, plain, (![E_188, A_190, B_189, D_187, C_186]: (v1_funct_2(k8_funct_2(A_190, B_189, C_186, D_187, E_188), A_190, C_186) | ~m1_subset_1(E_188, k1_zfmisc_1(k2_zfmisc_1(B_189, C_186))) | ~v1_funct_1(E_188) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))) | ~v1_funct_2(D_187, A_190, B_189) | ~v1_funct_1(D_187))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.36/2.22  tff(c_669, plain, (![A_190, D_187]: (v1_funct_2(k8_funct_2(A_190, '#skF_1', '#skF_3', D_187, '#skF_5'), A_190, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(A_190, '#skF_1'))) | ~v1_funct_2(D_187, A_190, '#skF_1') | ~v1_funct_1(D_187))), inference(resolution, [status(thm)], [c_52, c_658])).
% 6.36/2.22  tff(c_696, plain, (![A_193, D_194]: (v1_funct_2(k8_funct_2(A_193, '#skF_1', '#skF_3', D_194, '#skF_5'), A_193, '#skF_3') | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_193, '#skF_1'))) | ~v1_funct_2(D_194, A_193, '#skF_1') | ~v1_funct_1(D_194))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_669])).
% 6.36/2.22  tff(c_707, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_696])).
% 6.36/2.22  tff(c_715, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_707])).
% 6.36/2.22  tff(c_69, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_56, c_66])).
% 6.36/2.22  tff(c_75, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 6.36/2.22  tff(c_92, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_85])).
% 6.36/2.22  tff(c_145, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.36/2.22  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_145])).
% 6.36/2.22  tff(c_1002, plain, (![E_216, D_211, C_214, B_213, F_215, A_212]: (k7_partfun1(A_212, E_216, k1_funct_1(D_211, F_215))=k1_funct_1(k8_funct_2(B_213, C_214, A_212, D_211, E_216), F_215) | k1_xboole_0=B_213 | ~r1_tarski(k2_relset_1(B_213, C_214, D_211), k1_relset_1(C_214, A_212, E_216)) | ~m1_subset_1(F_215, B_213) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(C_214, A_212))) | ~v1_funct_1(E_216) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(B_213, C_214))) | ~v1_funct_2(D_211, B_213, C_214) | ~v1_funct_1(D_211) | v1_xboole_0(C_214))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.36/2.22  tff(c_1010, plain, (![A_212, E_216, F_215]: (k7_partfun1(A_212, E_216, k1_funct_1('#skF_4', F_215))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_212, '#skF_4', E_216), F_215) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_212, E_216)) | ~m1_subset_1(F_215, '#skF_2') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_212))) | ~v1_funct_1(E_216) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_1002])).
% 6.36/2.22  tff(c_1019, plain, (![A_212, E_216, F_215]: (k7_partfun1(A_212, E_216, k1_funct_1('#skF_4', F_215))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_212, '#skF_4', E_216), F_215) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_212, E_216)) | ~m1_subset_1(F_215, '#skF_2') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_212))) | ~v1_funct_1(E_216) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1010])).
% 6.36/2.22  tff(c_1020, plain, (![A_212, E_216, F_215]: (k7_partfun1(A_212, E_216, k1_funct_1('#skF_4', F_215))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_212, '#skF_4', E_216), F_215) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_212, E_216)) | ~m1_subset_1(F_215, '#skF_2') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_212))) | ~v1_funct_1(E_216))), inference(negUnitSimplification, [status(thm)], [c_64, c_1019])).
% 6.36/2.22  tff(c_1409, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1020])).
% 6.36/2.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.36/2.22  tff(c_1411, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_2])).
% 6.36/2.22  tff(c_1413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1411])).
% 6.36/2.22  tff(c_1415, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1020])).
% 6.36/2.22  tff(c_117, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.36/2.22  tff(c_125, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_52, c_117])).
% 6.36/2.22  tff(c_139, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_125])).
% 6.36/2.22  tff(c_1012, plain, (![D_211, F_215, B_213]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1(D_211, F_215))=k1_funct_1(k8_funct_2(B_213, '#skF_1', '#skF_3', D_211, '#skF_5'), F_215) | k1_xboole_0=B_213 | ~r1_tarski(k2_relset_1(B_213, '#skF_1', D_211), '#skF_1') | ~m1_subset_1(F_215, B_213) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(B_213, '#skF_1'))) | ~v1_funct_2(D_211, B_213, '#skF_1') | ~v1_funct_1(D_211) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_1002])).
% 6.36/2.22  tff(c_1022, plain, (![D_211, F_215, B_213]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1(D_211, F_215))=k1_funct_1(k8_funct_2(B_213, '#skF_1', '#skF_3', D_211, '#skF_5'), F_215) | k1_xboole_0=B_213 | ~r1_tarski(k2_relset_1(B_213, '#skF_1', D_211), '#skF_1') | ~m1_subset_1(F_215, B_213) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(B_213, '#skF_1'))) | ~v1_funct_2(D_211, B_213, '#skF_1') | ~v1_funct_1(D_211) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1012])).
% 6.36/2.22  tff(c_2212, plain, (![D_317, F_318, B_319]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1(D_317, F_318))=k1_funct_1(k8_funct_2(B_319, '#skF_1', '#skF_3', D_317, '#skF_5'), F_318) | k1_xboole_0=B_319 | ~r1_tarski(k2_relset_1(B_319, '#skF_1', D_317), '#skF_1') | ~m1_subset_1(F_318, B_319) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(B_319, '#skF_1'))) | ~v1_funct_2(D_317, B_319, '#skF_1') | ~v1_funct_1(D_317))), inference(negUnitSimplification, [status(thm)], [c_64, c_1022])).
% 6.36/2.22  tff(c_2235, plain, (![F_318]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_318))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_318) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_318, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_2212])).
% 6.36/2.22  tff(c_2247, plain, (![F_318]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_318))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_318) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_318, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_152, c_2235])).
% 6.36/2.22  tff(c_2248, plain, (![F_318]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_318))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_318) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_318, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1415, c_2247])).
% 6.36/2.22  tff(c_2250, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_2248])).
% 6.36/2.22  tff(c_2253, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_2250])).
% 6.36/2.22  tff(c_2257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_92, c_2253])).
% 6.36/2.22  tff(c_2364, plain, (![F_326]: (k7_partfun1('#skF_3', '#skF_5', k1_funct_1('#skF_4', F_326))=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_326) | ~m1_subset_1(F_326, '#skF_2'))), inference(splitRight, [status(thm)], [c_2248])).
% 6.36/2.22  tff(c_2374, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2364, c_985])).
% 6.36/2.22  tff(c_2386, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2374])).
% 6.36/2.22  tff(c_28, plain, (![C_29, D_30, B_28, A_27, E_31]: (m1_subset_1(k8_funct_2(A_27, B_28, C_29, D_30, E_31), k1_zfmisc_1(k2_zfmisc_1(A_27, C_29))) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(B_28, C_29))) | ~v1_funct_1(E_31) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_2(D_30, A_27, B_28) | ~v1_funct_1(D_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.36/2.22  tff(c_767, plain, (![A_202, D_199, E_200, C_198, B_201]: (m1_subset_1(k8_funct_2(A_202, B_201, C_198, D_199, E_200), k1_zfmisc_1(k2_zfmisc_1(A_202, C_198))) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(B_201, C_198))) | ~v1_funct_1(E_200) | ~m1_subset_1(D_199, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))) | ~v1_funct_2(D_199, A_202, B_201) | ~v1_funct_1(D_199))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.36/2.22  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.36/2.22  tff(c_2306, plain, (![C_323, D_324, A_325, B_321, E_322]: (k1_relset_1(A_325, C_323, k8_funct_2(A_325, B_321, C_323, D_324, E_322))=k1_relat_1(k8_funct_2(A_325, B_321, C_323, D_324, E_322)) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(B_321, C_323))) | ~v1_funct_1(E_322) | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_325, B_321))) | ~v1_funct_2(D_324, A_325, B_321) | ~v1_funct_1(D_324))), inference(resolution, [status(thm)], [c_767, c_16])).
% 6.36/2.22  tff(c_2328, plain, (![A_325, D_324]: (k1_relset_1(A_325, '#skF_3', k8_funct_2(A_325, '#skF_1', '#skF_3', D_324, '#skF_5'))=k1_relat_1(k8_funct_2(A_325, '#skF_1', '#skF_3', D_324, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_324, k1_zfmisc_1(k2_zfmisc_1(A_325, '#skF_1'))) | ~v1_funct_2(D_324, A_325, '#skF_1') | ~v1_funct_1(D_324))), inference(resolution, [status(thm)], [c_52, c_2306])).
% 6.36/2.22  tff(c_2634, plain, (![A_360, D_361]: (k1_relset_1(A_360, '#skF_3', k8_funct_2(A_360, '#skF_1', '#skF_3', D_361, '#skF_5'))=k1_relat_1(k8_funct_2(A_360, '#skF_1', '#skF_3', D_361, '#skF_5')) | ~m1_subset_1(D_361, k1_zfmisc_1(k2_zfmisc_1(A_360, '#skF_1'))) | ~v1_funct_2(D_361, A_360, '#skF_1') | ~v1_funct_1(D_361))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2328])).
% 6.36/2.22  tff(c_2657, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_2634])).
% 6.36/2.22  tff(c_2669, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2657])).
% 6.36/2.22  tff(c_38, plain, (![B_52, F_67, E_65, D_61, C_53, A_51]: (k7_partfun1(A_51, E_65, k1_funct_1(D_61, F_67))=k1_funct_1(k8_funct_2(B_52, C_53, A_51, D_61, E_65), F_67) | k1_xboole_0=B_52 | ~r1_tarski(k2_relset_1(B_52, C_53, D_61), k1_relset_1(C_53, A_51, E_65)) | ~m1_subset_1(F_67, B_52) | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(C_53, A_51))) | ~v1_funct_1(E_65) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(B_52, C_53))) | ~v1_funct_2(D_61, B_52, C_53) | ~v1_funct_1(D_61) | v1_xboole_0(C_53))), inference(cnfTransformation, [status(thm)], [f_159])).
% 6.36/2.22  tff(c_2672, plain, (![D_61, F_67, B_52]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_61, F_67))=k1_funct_1(k8_funct_2(B_52, '#skF_2', '#skF_3', D_61, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_67) | k1_xboole_0=B_52 | ~r1_tarski(k2_relset_1(B_52, '#skF_2', D_61), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_67, B_52) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(B_52, '#skF_2'))) | ~v1_funct_2(D_61, B_52, '#skF_2') | ~v1_funct_1(D_61) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2669, c_38])).
% 6.36/2.22  tff(c_2676, plain, (![D_61, F_67, B_52]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_61, F_67))=k1_funct_1(k8_funct_2(B_52, '#skF_2', '#skF_3', D_61, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_67) | k1_xboole_0=B_52 | ~r1_tarski(k2_relset_1(B_52, '#skF_2', D_61), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_67, B_52) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(B_52, '#skF_2'))) | ~v1_funct_2(D_61, B_52, '#skF_2') | ~v1_funct_1(D_61) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_2672])).
% 6.36/2.22  tff(c_2677, plain, (![D_61, F_67, B_52]: (k7_partfun1('#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_61, F_67))=k1_funct_1(k8_funct_2(B_52, '#skF_2', '#skF_3', D_61, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_67) | k1_xboole_0=B_52 | ~r1_tarski(k2_relset_1(B_52, '#skF_2', D_61), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_67, B_52) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(B_52, '#skF_2'))) | ~v1_funct_2(D_61, B_52, '#skF_2') | ~v1_funct_1(D_61))), inference(negUnitSimplification, [status(thm)], [c_62, c_2676])).
% 6.36/2.22  tff(c_2771, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2677])).
% 6.36/2.22  tff(c_2774, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2771])).
% 6.36/2.22  tff(c_2778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_2774])).
% 6.36/2.22  tff(c_2780, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2677])).
% 6.36/2.22  tff(c_368, plain, (![B_148, C_149]: (k3_funct_2('#skF_2', B_148, C_149, '#skF_6')=k1_funct_1(C_149, '#skF_6') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_148))) | ~v1_funct_2(C_149, '#skF_2', B_148) | ~v1_funct_1(C_149))), inference(negUnitSimplification, [status(thm)], [c_62, c_355])).
% 6.36/2.22  tff(c_2800, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2780, c_368])).
% 6.36/2.22  tff(c_2850, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_715, c_2386, c_2800])).
% 6.36/2.22  tff(c_2852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_986, c_2850])).
% 6.36/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.36/2.22  
% 6.36/2.22  Inference rules
% 6.36/2.22  ----------------------
% 6.36/2.22  #Ref     : 0
% 6.36/2.22  #Sup     : 579
% 6.36/2.22  #Fact    : 0
% 6.36/2.22  #Define  : 0
% 6.36/2.22  #Split   : 14
% 6.36/2.22  #Chain   : 0
% 6.36/2.22  #Close   : 0
% 6.36/2.22  
% 6.36/2.22  Ordering : KBO
% 6.36/2.22  
% 6.36/2.22  Simplification rules
% 6.36/2.22  ----------------------
% 6.36/2.22  #Subsume      : 69
% 6.36/2.22  #Demod        : 414
% 6.36/2.22  #Tautology    : 90
% 6.36/2.22  #SimpNegUnit  : 46
% 6.36/2.22  #BackRed      : 5
% 6.36/2.22  
% 6.36/2.22  #Partial instantiations: 0
% 6.36/2.22  #Strategies tried      : 1
% 6.36/2.22  
% 6.36/2.22  Timing (in seconds)
% 6.36/2.22  ----------------------
% 6.36/2.23  Preprocessing        : 0.36
% 6.36/2.23  Parsing              : 0.19
% 6.36/2.23  CNF conversion       : 0.03
% 6.36/2.23  Main loop            : 1.05
% 6.36/2.23  Inferencing          : 0.35
% 6.36/2.23  Reduction            : 0.36
% 6.36/2.23  Demodulation         : 0.25
% 6.36/2.23  BG Simplification    : 0.05
% 6.36/2.23  Subsumption          : 0.21
% 6.36/2.23  Abstraction          : 0.07
% 6.36/2.23  MUC search           : 0.00
% 6.36/2.23  Cooper               : 0.00
% 6.36/2.23  Total                : 1.50
% 6.36/2.23  Index Insertion      : 0.00
% 6.36/2.23  Index Deletion       : 0.00
% 6.36/2.23  Index Matching       : 0.00
% 6.36/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
