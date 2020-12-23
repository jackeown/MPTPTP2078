%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:11 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 505 expanded)
%              Number of leaves         :   42 ( 186 expanded)
%              Depth                    :   15
%              Number of atoms          :  265 (1806 expanded)
%              Number of equality atoms :   24 ( 126 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                   => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_24,plain,(
    ! [A_25] :
      ( l1_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_59,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_70,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_70])).

tff(c_92,plain,(
    ! [B_92,A_93] :
      ( k1_relat_1(B_92) = A_93
      | ~ v1_partfun1(B_92,A_93)
      | ~ v4_relat_1(B_92,A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_92])).

tff(c_98,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_95])).

tff(c_99,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_115,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_partfun1(C_99,A_100)
      | ~ v1_funct_2(C_99,A_100,B_101)
      | ~ v1_funct_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | v1_xboole_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_121,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_118])).

tff(c_122,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_121])).

tff(c_26,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_125,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_122,c_26])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_125])).

tff(c_131,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131])).

tff(c_136,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_143,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_38])).

tff(c_142,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_36])).

tff(c_257,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( r2_funct_2(A_120,B_121,C_122,C_122)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_2(D_123,A_120,B_121)
      | ~ v1_funct_1(D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_2(C_122,A_120,B_121)
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_259,plain,(
    ! [C_122] :
      ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),C_122,C_122)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_142,c_257])).

tff(c_275,plain,(
    ! [C_126] :
      ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),C_126,C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_126,k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_143,c_259])).

tff(c_277,plain,
    ( r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_275])).

tff(c_280,plain,(
    r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_143,c_277])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_75,plain,(
    ! [B_89,A_90] :
      ( k7_relat_1(B_89,A_90) = B_89
      | ~ v4_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_75])).

tff(c_81,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_78])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_4,A_3)),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_89,plain,(
    r1_tarski(k1_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_85])).

tff(c_138,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_89])).

tff(c_225,plain,(
    ! [B_110,C_111,A_112] :
      ( m1_pre_topc(B_110,C_111)
      | ~ r1_tarski(u1_struct_0(B_110),u1_struct_0(C_111))
      | ~ m1_pre_topc(C_111,A_112)
      | ~ m1_pre_topc(B_110,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_242,plain,(
    ! [C_117,A_118] :
      ( m1_pre_topc('#skF_3',C_117)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(C_117))
      | ~ m1_pre_topc(C_117,A_118)
      | ~ m1_pre_topc('#skF_3',A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_225])).

tff(c_244,plain,(
    ! [A_118] :
      ( m1_pre_topc('#skF_3','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_118)
      | ~ m1_pre_topc('#skF_3',A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_242])).

tff(c_246,plain,(
    ! [A_118] :
      ( m1_pre_topc('#skF_3','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_244])).

tff(c_248,plain,(
    ! [A_119] :
      ( ~ m1_pre_topc('#skF_3',A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_251,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_251])).

tff(c_256,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_139,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_81])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( k2_partfun1(A_17,B_18,C_19,D_20) = k7_relat_1(C_19,D_20)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_194,plain,(
    ! [D_20] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',D_20) = k7_relat_1('#skF_4',D_20)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_142,c_20])).

tff(c_209,plain,(
    ! [D_20] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',D_20) = k7_relat_1('#skF_4',D_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_194])).

tff(c_281,plain,(
    ! [D_130,A_131,E_129,C_127,B_128] :
      ( k3_tmap_1(A_131,B_128,C_127,D_130,E_129) = k2_partfun1(u1_struct_0(C_127),u1_struct_0(B_128),E_129,u1_struct_0(D_130))
      | ~ m1_pre_topc(D_130,C_127)
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127),u1_struct_0(B_128))))
      | ~ v1_funct_2(E_129,u1_struct_0(C_127),u1_struct_0(B_128))
      | ~ v1_funct_1(E_129)
      | ~ m1_pre_topc(D_130,A_131)
      | ~ m1_pre_topc(C_127,A_131)
      | ~ l1_pre_topc(B_128)
      | ~ v2_pre_topc(B_128)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_283,plain,(
    ! [A_131,B_128,D_130,E_129] :
      ( k3_tmap_1(A_131,B_128,'#skF_3',D_130,E_129) = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_128),E_129,u1_struct_0(D_130))
      | ~ m1_pre_topc(D_130,'#skF_3')
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_128))))
      | ~ v1_funct_2(E_129,u1_struct_0('#skF_3'),u1_struct_0(B_128))
      | ~ v1_funct_1(E_129)
      | ~ m1_pre_topc(D_130,A_131)
      | ~ m1_pre_topc('#skF_3',A_131)
      | ~ l1_pre_topc(B_128)
      | ~ v2_pre_topc(B_128)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_281])).

tff(c_289,plain,(
    ! [A_132,B_133,D_134,E_135] :
      ( k3_tmap_1(A_132,B_133,'#skF_3',D_134,E_135) = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_133),E_135,u1_struct_0(D_134))
      | ~ m1_pre_topc(D_134,'#skF_3')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_133))))
      | ~ v1_funct_2(E_135,k1_relat_1('#skF_4'),u1_struct_0(B_133))
      | ~ v1_funct_1(E_135)
      | ~ m1_pre_topc(D_134,A_132)
      | ~ m1_pre_topc('#skF_3',A_132)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_136,c_283])).

tff(c_291,plain,(
    ! [A_132,D_134] :
      ( k3_tmap_1(A_132,'#skF_2','#skF_3',D_134,'#skF_4') = k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_134))
      | ~ m1_pre_topc(D_134,'#skF_3')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_134,A_132)
      | ~ m1_pre_topc('#skF_3',A_132)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_142,c_289])).

tff(c_296,plain,(
    ! [D_134,A_132] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_134)) = k3_tmap_1(A_132,'#skF_2','#skF_3',D_134,'#skF_4')
      | ~ m1_pre_topc(D_134,'#skF_3')
      | ~ m1_pre_topc(D_134,A_132)
      | ~ m1_pre_topc('#skF_3',A_132)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_143,c_209,c_291])).

tff(c_300,plain,(
    ! [D_136,A_137] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_136)) = k3_tmap_1(A_137,'#skF_2','#skF_3',D_136,'#skF_4')
      | ~ m1_pre_topc(D_136,'#skF_3')
      | ~ m1_pre_topc(D_136,A_137)
      | ~ m1_pre_topc('#skF_3',A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_296])).

tff(c_304,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_300])).

tff(c_311,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_42,c_256,c_139,c_136,c_304])).

tff(c_312,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_311])).

tff(c_34,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_141,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_34])).

tff(c_313,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_141])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:54:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.44  
% 2.57/1.44  %Foreground sorts:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Background operators:
% 2.57/1.44  
% 2.57/1.44  
% 2.57/1.44  %Foreground operators:
% 2.57/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.57/1.44  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.57/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.57/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.57/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.57/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.57/1.44  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.57/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.57/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.57/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.44  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.57/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.44  
% 2.57/1.46  tff(f_176, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 2.57/1.46  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/1.46  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.57/1.46  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.57/1.46  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.57/1.46  tff(f_59, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.57/1.46  tff(f_99, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.57/1.46  tff(f_87, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 2.57/1.46  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.57/1.46  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.57/1.46  tff(f_145, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.57/1.46  tff(f_73, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.57/1.46  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.57/1.46  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_24, plain, (![A_25]: (l1_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.57/1.46  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_59, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.46  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_59])).
% 2.57/1.46  tff(c_70, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.46  tff(c_74, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_70])).
% 2.57/1.46  tff(c_92, plain, (![B_92, A_93]: (k1_relat_1(B_92)=A_93 | ~v1_partfun1(B_92, A_93) | ~v4_relat_1(B_92, A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.57/1.46  tff(c_95, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_92])).
% 2.57/1.46  tff(c_98, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_95])).
% 2.57/1.46  tff(c_99, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_98])).
% 2.57/1.46  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_115, plain, (![C_99, A_100, B_101]: (v1_partfun1(C_99, A_100) | ~v1_funct_2(C_99, A_100, B_101) | ~v1_funct_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | v1_xboole_0(B_101))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.46  tff(c_118, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_115])).
% 2.57/1.46  tff(c_121, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_118])).
% 2.57/1.46  tff(c_122, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_99, c_121])).
% 2.57/1.46  tff(c_26, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.57/1.46  tff(c_125, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_122, c_26])).
% 2.57/1.46  tff(c_128, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_125])).
% 2.57/1.46  tff(c_131, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_128])).
% 2.57/1.46  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_131])).
% 2.57/1.46  tff(c_136, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 2.57/1.46  tff(c_143, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_38])).
% 2.57/1.46  tff(c_142, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_36])).
% 2.57/1.46  tff(c_257, plain, (![A_120, B_121, C_122, D_123]: (r2_funct_2(A_120, B_121, C_122, C_122) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_2(D_123, A_120, B_121) | ~v1_funct_1(D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_2(C_122, A_120, B_121) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.57/1.46  tff(c_259, plain, (![C_122]: (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), C_122, C_122) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_122))), inference(resolution, [status(thm)], [c_142, c_257])).
% 2.57/1.46  tff(c_275, plain, (![C_126]: (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), C_126, C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_126, k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_126))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_143, c_259])).
% 2.57/1.46  tff(c_277, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_275])).
% 2.57/1.46  tff(c_280, plain, (r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_143, c_277])).
% 2.57/1.46  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_75, plain, (![B_89, A_90]: (k7_relat_1(B_89, A_90)=B_89 | ~v4_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.46  tff(c_78, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_75])).
% 2.57/1.46  tff(c_81, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_78])).
% 2.57/1.46  tff(c_4, plain, (![B_4, A_3]: (r1_tarski(k1_relat_1(k7_relat_1(B_4, A_3)), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.46  tff(c_85, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81, c_4])).
% 2.57/1.46  tff(c_89, plain, (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_85])).
% 2.57/1.46  tff(c_138, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_89])).
% 2.57/1.46  tff(c_225, plain, (![B_110, C_111, A_112]: (m1_pre_topc(B_110, C_111) | ~r1_tarski(u1_struct_0(B_110), u1_struct_0(C_111)) | ~m1_pre_topc(C_111, A_112) | ~m1_pre_topc(B_110, A_112) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_145])).
% 2.57/1.46  tff(c_242, plain, (![C_117, A_118]: (m1_pre_topc('#skF_3', C_117) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(C_117)) | ~m1_pre_topc(C_117, A_118) | ~m1_pre_topc('#skF_3', A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(superposition, [status(thm), theory('equality')], [c_136, c_225])).
% 2.57/1.46  tff(c_244, plain, (![A_118]: (m1_pre_topc('#skF_3', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_118) | ~m1_pre_topc('#skF_3', A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(superposition, [status(thm), theory('equality')], [c_136, c_242])).
% 2.57/1.46  tff(c_246, plain, (![A_118]: (m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_244])).
% 2.57/1.46  tff(c_248, plain, (![A_119]: (~m1_pre_topc('#skF_3', A_119) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(splitLeft, [status(thm)], [c_246])).
% 2.57/1.46  tff(c_251, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_248])).
% 2.57/1.46  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_251])).
% 2.57/1.46  tff(c_256, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_246])).
% 2.57/1.46  tff(c_139, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_81])).
% 2.57/1.46  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_20, plain, (![A_17, B_18, C_19, D_20]: (k2_partfun1(A_17, B_18, C_19, D_20)=k7_relat_1(C_19, D_20) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.57/1.46  tff(c_194, plain, (![D_20]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', D_20)=k7_relat_1('#skF_4', D_20) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_142, c_20])).
% 2.57/1.46  tff(c_209, plain, (![D_20]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', D_20)=k7_relat_1('#skF_4', D_20))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_194])).
% 2.57/1.46  tff(c_281, plain, (![D_130, A_131, E_129, C_127, B_128]: (k3_tmap_1(A_131, B_128, C_127, D_130, E_129)=k2_partfun1(u1_struct_0(C_127), u1_struct_0(B_128), E_129, u1_struct_0(D_130)) | ~m1_pre_topc(D_130, C_127) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127), u1_struct_0(B_128)))) | ~v1_funct_2(E_129, u1_struct_0(C_127), u1_struct_0(B_128)) | ~v1_funct_1(E_129) | ~m1_pre_topc(D_130, A_131) | ~m1_pre_topc(C_127, A_131) | ~l1_pre_topc(B_128) | ~v2_pre_topc(B_128) | v2_struct_0(B_128) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.57/1.46  tff(c_283, plain, (![A_131, B_128, D_130, E_129]: (k3_tmap_1(A_131, B_128, '#skF_3', D_130, E_129)=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_128), E_129, u1_struct_0(D_130)) | ~m1_pre_topc(D_130, '#skF_3') | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_128)))) | ~v1_funct_2(E_129, u1_struct_0('#skF_3'), u1_struct_0(B_128)) | ~v1_funct_1(E_129) | ~m1_pre_topc(D_130, A_131) | ~m1_pre_topc('#skF_3', A_131) | ~l1_pre_topc(B_128) | ~v2_pre_topc(B_128) | v2_struct_0(B_128) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(superposition, [status(thm), theory('equality')], [c_136, c_281])).
% 2.57/1.46  tff(c_289, plain, (![A_132, B_133, D_134, E_135]: (k3_tmap_1(A_132, B_133, '#skF_3', D_134, E_135)=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_133), E_135, u1_struct_0(D_134)) | ~m1_pre_topc(D_134, '#skF_3') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_133)))) | ~v1_funct_2(E_135, k1_relat_1('#skF_4'), u1_struct_0(B_133)) | ~v1_funct_1(E_135) | ~m1_pre_topc(D_134, A_132) | ~m1_pre_topc('#skF_3', A_132) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_136, c_283])).
% 2.57/1.46  tff(c_291, plain, (![A_132, D_134]: (k3_tmap_1(A_132, '#skF_2', '#skF_3', D_134, '#skF_4')=k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_134)) | ~m1_pre_topc(D_134, '#skF_3') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_134, A_132) | ~m1_pre_topc('#skF_3', A_132) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_142, c_289])).
% 2.57/1.46  tff(c_296, plain, (![D_134, A_132]: (k7_relat_1('#skF_4', u1_struct_0(D_134))=k3_tmap_1(A_132, '#skF_2', '#skF_3', D_134, '#skF_4') | ~m1_pre_topc(D_134, '#skF_3') | ~m1_pre_topc(D_134, A_132) | ~m1_pre_topc('#skF_3', A_132) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_143, c_209, c_291])).
% 2.57/1.46  tff(c_300, plain, (![D_136, A_137]: (k7_relat_1('#skF_4', u1_struct_0(D_136))=k3_tmap_1(A_137, '#skF_2', '#skF_3', D_136, '#skF_4') | ~m1_pre_topc(D_136, '#skF_3') | ~m1_pre_topc(D_136, A_137) | ~m1_pre_topc('#skF_3', A_137) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(negUnitSimplification, [status(thm)], [c_50, c_296])).
% 2.57/1.46  tff(c_304, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_300])).
% 2.57/1.46  tff(c_311, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_42, c_256, c_139, c_136, c_304])).
% 2.57/1.46  tff(c_312, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_311])).
% 2.57/1.46  tff(c_34, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 2.57/1.46  tff(c_141, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_34])).
% 2.57/1.46  tff(c_313, plain, (~r2_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_141])).
% 2.57/1.46  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_313])).
% 2.57/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.46  
% 2.57/1.46  Inference rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Ref     : 0
% 2.57/1.46  #Sup     : 48
% 2.57/1.46  #Fact    : 0
% 2.57/1.46  #Define  : 0
% 2.57/1.46  #Split   : 3
% 2.57/1.46  #Chain   : 0
% 2.57/1.46  #Close   : 0
% 2.57/1.46  
% 2.57/1.46  Ordering : KBO
% 2.57/1.46  
% 2.57/1.46  Simplification rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Subsume      : 5
% 2.57/1.46  #Demod        : 66
% 2.57/1.46  #Tautology    : 22
% 2.57/1.46  #SimpNegUnit  : 8
% 2.57/1.46  #BackRed      : 7
% 2.57/1.46  
% 2.57/1.46  #Partial instantiations: 0
% 2.57/1.46  #Strategies tried      : 1
% 2.57/1.46  
% 2.57/1.46  Timing (in seconds)
% 2.57/1.46  ----------------------
% 2.57/1.47  Preprocessing        : 0.38
% 2.57/1.47  Parsing              : 0.20
% 2.57/1.47  CNF conversion       : 0.04
% 2.57/1.47  Main loop            : 0.27
% 2.57/1.47  Inferencing          : 0.09
% 2.57/1.47  Reduction            : 0.09
% 2.57/1.47  Demodulation         : 0.06
% 2.57/1.47  BG Simplification    : 0.02
% 2.57/1.47  Subsumption          : 0.04
% 2.57/1.47  Abstraction          : 0.02
% 2.57/1.47  MUC search           : 0.00
% 2.57/1.47  Cooper               : 0.00
% 2.57/1.47  Total                : 0.70
% 2.57/1.47  Index Insertion      : 0.00
% 2.57/1.47  Index Deletion       : 0.00
% 2.57/1.47  Index Matching       : 0.00
% 2.57/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
