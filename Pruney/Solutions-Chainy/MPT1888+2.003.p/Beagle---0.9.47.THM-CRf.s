%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:21 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 580 expanded)
%              Number of leaves         :   40 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          :  220 (1686 expanded)
%              Number of equality atoms :   23 ( 268 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
                  | k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_33,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_xboole_0(B,C)
                  & v3_pre_topc(B,A) )
               => r1_xboole_0(B,k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)))
               => k2_pre_topc(A,k6_domain_1(u1_struct_0(A),B)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_6,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_tarski(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [B_55,A_56] :
      ( m1_subset_1(k1_tarski(B_55),k1_zfmisc_1(A_56))
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(B_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_70,plain,(
    ! [B_55,A_56] :
      ( v1_xboole_0(k1_tarski(B_55))
      | ~ v1_xboole_0(A_56)
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(B_55,A_56) ) ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_74,plain,(
    ! [A_57,B_58] :
      ( ~ v1_xboole_0(A_57)
      | k1_xboole_0 = A_57
      | ~ m1_subset_1(B_58,A_57) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_70])).

tff(c_85,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_74])).

tff(c_87,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_89,plain,(
    ! [A_60,B_61] :
      ( k6_domain_1(A_60,B_61) = k1_tarski(B_61)
      | ~ m1_subset_1(B_61,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_98,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_89])).

tff(c_105,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_98])).

tff(c_95,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_102,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_95])).

tff(c_38,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_107,plain,(
    k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) != k2_pre_topc('#skF_2',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_38])).

tff(c_167,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) != k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_107])).

tff(c_57,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(k1_tarski(A_48),B_49)
      | r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ! [B_49,A_48] :
      ( r1_xboole_0(B_49,k1_tarski(A_48))
      | r2_hidden(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_57,c_4])).

tff(c_112,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k6_domain_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_112])).

tff(c_129,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_124])).

tff(c_130,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_129])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_pre_topc(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_235,plain,(
    ! [A_70,B_71] :
      ( v4_pre_topc(k2_pre_topc(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_241,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_235])).

tff(c_254,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_241])).

tff(c_330,plain,(
    ! [B_77,A_78] :
      ( v3_pre_topc(B_77,A_78)
      | ~ v4_pre_topc(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v3_tdlat_3(A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_818,plain,(
    ! [A_111,B_112] :
      ( v3_pre_topc(k2_pre_topc(A_111,B_112),A_111)
      | ~ v4_pre_topc(k2_pre_topc(A_111,B_112),A_111)
      | ~ v3_tdlat_3(A_111)
      | ~ v2_pre_topc(A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(resolution,[status(thm)],[c_14,c_330])).

tff(c_828,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_254,c_818])).

tff(c_837,plain,(
    v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130,c_50,c_48,c_828])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_134,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_20])).

tff(c_138,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_139,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_138])).

tff(c_446,plain,(
    ! [B_87,A_88,C_89] :
      ( r1_xboole_0(B_87,k2_pre_topc(A_88,C_89))
      | ~ v3_pre_topc(B_87,A_88)
      | ~ r1_xboole_0(B_87,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_452,plain,(
    ! [B_87] :
      ( r1_xboole_0(B_87,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_87,'#skF_2')
      | ~ r1_xboole_0(B_87,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_139,c_446])).

tff(c_678,plain,(
    ! [B_102] :
      ( r1_xboole_0(B_102,k2_pre_topc('#skF_2',k1_tarski('#skF_4')))
      | ~ v3_pre_topc(B_102,'#skF_2')
      | ~ r1_xboole_0(B_102,k1_tarski('#skF_4'))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_452])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_106,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_40])).

tff(c_169,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k2_pre_topc('#skF_2',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_106])).

tff(c_684,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),'#skF_2')
    | ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_678,c_169])).

tff(c_842,plain,
    ( ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_684])).

tff(c_843,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_849,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_843])).

tff(c_853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130,c_849])).

tff(c_854,plain,(
    ~ r1_xboole_0(k2_pre_topc('#skF_2',k1_tarski('#skF_3')),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_865,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2',k1_tarski('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_60,c_854])).

tff(c_555,plain,(
    ! [A_94,C_95,B_96] :
      ( k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),C_95)) = k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),B_96))
      | ~ r2_hidden(B_96,k2_pre_topc(A_94,k6_domain_1(u1_struct_0(A_94),C_95)))
      | ~ m1_subset_1(C_95,u1_struct_0(A_94))
      | ~ m1_subset_1(B_96,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v3_tdlat_3(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_561,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_96)) = k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_555])).

tff(c_566,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_96)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_102,c_561])).

tff(c_567,plain,(
    ! [B_96] :
      ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),B_96)) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
      | ~ r2_hidden(B_96,k2_pre_topc('#skF_2',k1_tarski('#skF_3')))
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_566])).

tff(c_868,plain,
    ( k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_4')) = k2_pre_topc('#skF_2',k1_tarski('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_865,c_567])).

tff(c_871,plain,(
    k2_pre_topc('#skF_2',k1_tarski('#skF_3')) = k2_pre_topc('#skF_2',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_105,c_868])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_871])).

tff(c_874,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_18,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_882,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_874,c_18])).

tff(c_886,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_882])).

tff(c_887,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_886])).

tff(c_891,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_887])).

tff(c_895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  
% 3.22/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.50  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.22/1.50  
% 3.22/1.50  %Foreground sorts:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Background operators:
% 3.22/1.50  
% 3.22/1.50  
% 3.22/1.50  %Foreground operators:
% 3.22/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.22/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.22/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.22/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.22/1.50  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.22/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.50  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.22/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.50  
% 3.38/1.52  tff(f_160, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) | (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 3.38/1.52  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.38/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/1.52  tff(f_33, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.38/1.52  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 3.38/1.52  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.38/1.52  tff(f_84, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.38/1.52  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 3.38/1.52  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.38/1.52  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.38/1.52  tff(f_58, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.38/1.52  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.38/1.52  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.38/1.52  tff(f_121, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_xboole_0(B, C) & v3_pre_topc(B, A)) => r1_xboole_0(B, k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 3.38/1.52  tff(f_140, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) => (k2_pre_topc(A, k6_domain_1(u1_struct_0(A), B)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 3.38/1.52  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.38/1.52  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.38/1.52  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.38/1.52  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_6, plain, (![A_3]: (~v1_xboole_0(k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.52  tff(c_67, plain, (![B_55, A_56]: (m1_subset_1(k1_tarski(B_55), k1_zfmisc_1(A_56)) | k1_xboole_0=A_56 | ~m1_subset_1(B_55, A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.38/1.52  tff(c_12, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.38/1.52  tff(c_70, plain, (![B_55, A_56]: (v1_xboole_0(k1_tarski(B_55)) | ~v1_xboole_0(A_56) | k1_xboole_0=A_56 | ~m1_subset_1(B_55, A_56))), inference(resolution, [status(thm)], [c_67, c_12])).
% 3.38/1.52  tff(c_74, plain, (![A_57, B_58]: (~v1_xboole_0(A_57) | k1_xboole_0=A_57 | ~m1_subset_1(B_58, A_57))), inference(negUnitSimplification, [status(thm)], [c_6, c_70])).
% 3.38/1.52  tff(c_85, plain, (~v1_xboole_0(u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_74])).
% 3.38/1.52  tff(c_87, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_85])).
% 3.38/1.52  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_89, plain, (![A_60, B_61]: (k6_domain_1(A_60, B_61)=k1_tarski(B_61) | ~m1_subset_1(B_61, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.38/1.52  tff(c_98, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_89])).
% 3.38/1.52  tff(c_105, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_87, c_98])).
% 3.38/1.52  tff(c_95, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_89])).
% 3.38/1.52  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_87, c_95])).
% 3.38/1.52  tff(c_38, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_107, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_38])).
% 3.38/1.52  tff(c_167, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_107])).
% 3.38/1.52  tff(c_57, plain, (![A_48, B_49]: (r1_xboole_0(k1_tarski(A_48), B_49) | r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.52  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.38/1.52  tff(c_60, plain, (![B_49, A_48]: (r1_xboole_0(B_49, k1_tarski(A_48)) | r2_hidden(A_48, B_49))), inference(resolution, [status(thm)], [c_57, c_4])).
% 3.38/1.52  tff(c_112, plain, (![A_62, B_63]: (m1_subset_1(k6_domain_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.52  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_112])).
% 3.38/1.52  tff(c_129, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_124])).
% 3.38/1.52  tff(c_130, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_87, c_129])).
% 3.38/1.52  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k2_pre_topc(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.38/1.52  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_48, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_235, plain, (![A_70, B_71]: (v4_pre_topc(k2_pre_topc(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.38/1.52  tff(c_241, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_130, c_235])).
% 3.38/1.52  tff(c_254, plain, (v4_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_241])).
% 3.38/1.52  tff(c_330, plain, (![B_77, A_78]: (v3_pre_topc(B_77, A_78) | ~v4_pre_topc(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~v3_tdlat_3(A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.38/1.52  tff(c_818, plain, (![A_111, B_112]: (v3_pre_topc(k2_pre_topc(A_111, B_112), A_111) | ~v4_pre_topc(k2_pre_topc(A_111, B_112), A_111) | ~v3_tdlat_3(A_111) | ~v2_pre_topc(A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(resolution, [status(thm)], [c_14, c_330])).
% 3.38/1.52  tff(c_828, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_254, c_818])).
% 3.38/1.52  tff(c_837, plain, (v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_130, c_50, c_48, c_828])).
% 3.38/1.52  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k6_domain_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.52  tff(c_134, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_20])).
% 3.38/1.52  tff(c_138, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_134])).
% 3.38/1.52  tff(c_139, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_87, c_138])).
% 3.38/1.52  tff(c_446, plain, (![B_87, A_88, C_89]: (r1_xboole_0(B_87, k2_pre_topc(A_88, C_89)) | ~v3_pre_topc(B_87, A_88) | ~r1_xboole_0(B_87, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.38/1.52  tff(c_452, plain, (![B_87]: (r1_xboole_0(B_87, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_87, '#skF_2') | ~r1_xboole_0(B_87, k1_tarski('#skF_4')) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_139, c_446])).
% 3.38/1.52  tff(c_678, plain, (![B_102]: (r1_xboole_0(B_102, k2_pre_topc('#skF_2', k1_tarski('#skF_4'))) | ~v3_pre_topc(B_102, '#skF_2') | ~r1_xboole_0(B_102, k1_tarski('#skF_4')) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_452])).
% 3.38/1.52  tff(c_40, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.38/1.52  tff(c_106, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_40])).
% 3.38/1.52  tff(c_169, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k2_pre_topc('#skF_2', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_106])).
% 3.38/1.52  tff(c_684, plain, (~v3_pre_topc(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), '#skF_2') | ~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_678, c_169])).
% 3.38/1.52  tff(c_842, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_684])).
% 3.38/1.52  tff(c_843, plain, (~m1_subset_1(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_842])).
% 3.38/1.52  tff(c_849, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_843])).
% 3.38/1.52  tff(c_853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_130, c_849])).
% 3.38/1.52  tff(c_854, plain, (~r1_xboole_0(k2_pre_topc('#skF_2', k1_tarski('#skF_3')), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_842])).
% 3.38/1.52  tff(c_865, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', k1_tarski('#skF_3')))), inference(resolution, [status(thm)], [c_60, c_854])).
% 3.38/1.52  tff(c_555, plain, (![A_94, C_95, B_96]: (k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), C_95))=k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), B_96)) | ~r2_hidden(B_96, k2_pre_topc(A_94, k6_domain_1(u1_struct_0(A_94), C_95))) | ~m1_subset_1(C_95, u1_struct_0(A_94)) | ~m1_subset_1(B_96, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | ~v3_tdlat_3(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.38/1.52  tff(c_561, plain, (![B_96]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_96))=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')) | ~r2_hidden(B_96, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_555])).
% 3.38/1.52  tff(c_566, plain, (![B_96]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_96))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_96, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_102, c_561])).
% 3.38/1.52  tff(c_567, plain, (![B_96]: (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), B_96))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~r2_hidden(B_96, k2_pre_topc('#skF_2', k1_tarski('#skF_3'))) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_52, c_566])).
% 3.38/1.52  tff(c_868, plain, (k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_4'))=k2_pre_topc('#skF_2', k1_tarski('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_865, c_567])).
% 3.38/1.52  tff(c_871, plain, (k2_pre_topc('#skF_2', k1_tarski('#skF_3'))=k2_pre_topc('#skF_2', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_105, c_868])).
% 3.38/1.52  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_871])).
% 3.38/1.52  tff(c_874, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_85])).
% 3.38/1.52  tff(c_18, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.52  tff(c_882, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_874, c_18])).
% 3.38/1.52  tff(c_886, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_882])).
% 3.38/1.52  tff(c_887, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_886])).
% 3.38/1.52  tff(c_891, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_887])).
% 3.38/1.52  tff(c_895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_891])).
% 3.38/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.52  
% 3.38/1.52  Inference rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Ref     : 0
% 3.38/1.52  #Sup     : 171
% 3.38/1.52  #Fact    : 0
% 3.38/1.52  #Define  : 0
% 3.38/1.52  #Split   : 10
% 3.38/1.52  #Chain   : 0
% 3.38/1.52  #Close   : 0
% 3.38/1.52  
% 3.38/1.52  Ordering : KBO
% 3.38/1.52  
% 3.38/1.52  Simplification rules
% 3.38/1.52  ----------------------
% 3.38/1.52  #Subsume      : 26
% 3.38/1.52  #Demod        : 113
% 3.38/1.52  #Tautology    : 57
% 3.38/1.52  #SimpNegUnit  : 62
% 3.38/1.52  #BackRed      : 5
% 3.38/1.52  
% 3.38/1.52  #Partial instantiations: 0
% 3.38/1.52  #Strategies tried      : 1
% 3.38/1.52  
% 3.38/1.52  Timing (in seconds)
% 3.38/1.52  ----------------------
% 3.38/1.53  Preprocessing        : 0.34
% 3.38/1.53  Parsing              : 0.18
% 3.38/1.53  CNF conversion       : 0.02
% 3.38/1.53  Main loop            : 0.40
% 3.38/1.53  Inferencing          : 0.14
% 3.38/1.53  Reduction            : 0.13
% 3.38/1.53  Demodulation         : 0.08
% 3.38/1.53  BG Simplification    : 0.02
% 3.38/1.53  Subsumption          : 0.07
% 3.38/1.53  Abstraction          : 0.02
% 3.38/1.53  MUC search           : 0.00
% 3.38/1.53  Cooper               : 0.00
% 3.38/1.53  Total                : 0.77
% 3.38/1.53  Index Insertion      : 0.00
% 3.38/1.53  Index Deletion       : 0.00
% 3.38/1.53  Index Matching       : 0.00
% 3.38/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
