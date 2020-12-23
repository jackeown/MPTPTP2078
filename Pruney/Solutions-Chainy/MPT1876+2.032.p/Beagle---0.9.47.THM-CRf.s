%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 5.21s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 487 expanded)
%              Number of leaves         :   43 ( 185 expanded)
%              Depth                    :   22
%              Number of atoms          :  324 (1469 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_46,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_151,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_192,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_180,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B)
              & v2_tdlat_3(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_83,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | ~ r1_tarski(k1_tarski(A_61),B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,(
    ! [A_61] : r2_hidden(A_61,k1_tarski(A_61)) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_156,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,C_77)
      | ~ r1_tarski(B_78,C_77)
      | ~ r1_tarski(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_267,plain,(
    ! [A_89,B_90,A_91] :
      ( r1_tarski(A_89,B_90)
      | ~ r1_tarski(A_89,k1_tarski(A_91))
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_18,c_156])).

tff(c_412,plain,(
    ! [A_102,B_103,A_104] :
      ( r1_tarski(k1_tarski(A_102),B_103)
      | ~ r2_hidden(A_104,B_103)
      | ~ r2_hidden(A_102,k1_tarski(A_104)) ) ),
    inference(resolution,[status(thm)],[c_18,c_267])).

tff(c_439,plain,(
    ! [A_109,A_110] :
      ( r1_tarski(k1_tarski(A_109),A_110)
      | ~ r2_hidden(A_109,k1_tarski('#skF_1'(A_110)))
      | v1_xboole_0(A_110) ) ),
    inference(resolution,[status(thm)],[c_4,c_412])).

tff(c_455,plain,(
    ! [A_111] :
      ( r1_tarski(k1_tarski('#skF_1'(A_111)),A_111)
      | v1_xboole_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_109,c_439])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_127,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_166,plain,(
    ! [A_79] :
      ( r1_tarski(A_79,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_79,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_140,c_156])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | ~ r1_tarski(k1_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_185,plain,(
    ! [A_81] :
      ( r2_hidden(A_81,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_81),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_166,c_16])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_192,plain,(
    ! [A_81] :
      ( m1_subset_1(A_81,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_81),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_185,c_20])).

tff(c_475,plain,
    ( m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_455,c_192])).

tff(c_498,plain,(
    m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_475])).

tff(c_14,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_85,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_78])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,(
    ! [A_81] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_81),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_194,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_505,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_498,c_32])).

tff(c_508,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = k1_tarski('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_505])).

tff(c_299,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(A_95,B_94)
      | ~ v1_zfmisc_1(B_94)
      | v1_xboole_0(B_94)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_311,plain,(
    ! [A_11,B_12] :
      ( k1_tarski(A_11) = B_12
      | ~ v1_zfmisc_1(B_12)
      | v1_xboole_0(B_12)
      | v1_xboole_0(k1_tarski(A_11))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_18,c_299])).

tff(c_344,plain,(
    ! [A_97,B_98] :
      ( k1_tarski(A_97) = B_98
      | ~ v1_zfmisc_1(B_98)
      | v1_xboole_0(B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_311])).

tff(c_360,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_344])).

tff(c_450,plain,(
    ! [A_110] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_110)))),A_110)
      | v1_xboole_0(A_110)
      | v1_xboole_0(k1_tarski('#skF_1'(A_110))) ) ),
    inference(resolution,[status(thm)],[c_4,c_439])).

tff(c_521,plain,(
    ! [A_112] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_112)))),A_112)
      | v1_xboole_0(A_112) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_450])).

tff(c_541,plain,
    ( m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_521,c_192])).

tff(c_568,plain,(
    m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_541])).

tff(c_575,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k1_tarski('#skF_1'('#skF_4')))) = k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4'))))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_568,c_32])).

tff(c_581,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'(k1_tarski('#skF_1'('#skF_4')))) = k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_575])).

tff(c_715,plain,
    ( k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4')))) = k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_581])).

tff(c_723,plain,
    ( k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4')))) = k1_tarski('#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_508,c_715])).

tff(c_724,plain,(
    k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4')))) = k1_tarski('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_723])).

tff(c_454,plain,(
    ! [A_110] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_110)))),A_110)
      | v1_xboole_0(A_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_450])).

tff(c_751,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_4')),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_454])).

tff(c_799,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_4')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_751])).

tff(c_46,plain,(
    ! [B_40,A_38] :
      ( B_40 = A_38
      | ~ r1_tarski(A_38,B_40)
      | ~ v1_zfmisc_1(B_40)
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_819,plain,
    ( k1_tarski('#skF_1'('#skF_4')) = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_799,c_46])).

tff(c_838,plain,
    ( k1_tarski('#skF_1'('#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_819])).

tff(c_839,plain,(
    k1_tarski('#skF_1'('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_62,c_838])).

tff(c_851,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_508])).

tff(c_58,plain,(
    ! [A_47,B_49] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_47),B_49),A_47)
      | ~ m1_subset_1(B_49,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_992,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_4'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_58])).

tff(c_1002,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_498,c_992])).

tff(c_1004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_83,c_1002])).

tff(c_1026,plain,(
    ! [A_127] : ~ r1_tarski(k1_tarski(A_127),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_1032,plain,(
    ! [A_128] : ~ r2_hidden(A_128,'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1026])).

tff(c_1036,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1032])).

tff(c_1040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1036])).

tff(c_1041,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1043,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_78])).

tff(c_3772,plain,(
    ! [A_271,B_272] :
      ( m1_pre_topc('#skF_2'(A_271,B_272),A_271)
      | ~ v2_tex_2(B_272,A_271)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | v1_xboole_0(B_272)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3795,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3772])).

tff(c_3805,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1043,c_3795])).

tff(c_3806,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_3805])).

tff(c_28,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3819,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_3806,c_28])).

tff(c_3836,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3819])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_44,plain,(
    ! [B_37,A_35] :
      ( v2_tdlat_3(B_37)
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_tdlat_3(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3816,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3806,c_44])).

tff(c_3832,plain,
    ( v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_3816])).

tff(c_3833,plain,(
    v2_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_3832])).

tff(c_2760,plain,(
    ! [A_244,B_245] :
      ( ~ v2_struct_0('#skF_2'(A_244,B_245))
      | ~ v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | v1_xboole_0(B_245)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2791,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2760])).

tff(c_2801,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1043,c_2791])).

tff(c_2802,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_2801])).

tff(c_2939,plain,(
    ! [A_252,B_253] :
      ( v1_tdlat_3('#skF_2'(A_252,B_253))
      | ~ v2_tex_2(B_253,A_252)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | v1_xboole_0(B_253)
      | ~ l1_pre_topc(A_252)
      | ~ v2_pre_topc(A_252)
      | v2_struct_0(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2970,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_2939])).

tff(c_2980,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1043,c_2970])).

tff(c_2981,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_2980])).

tff(c_38,plain,(
    ! [B_33,A_31] :
      ( ~ v1_tdlat_3(B_33)
      | ~ v2_tdlat_3(B_33)
      | v7_struct_0(B_33)
      | v2_struct_0(B_33)
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3813,plain,
    ( ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3806,c_38])).

tff(c_3828,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2981,c_3813])).

tff(c_3829,plain,
    ( ~ v2_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2802,c_3828])).

tff(c_3842,plain,(
    v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3833,c_3829])).

tff(c_4265,plain,(
    ! [A_275,B_276] :
      ( u1_struct_0('#skF_2'(A_275,B_276)) = B_276
      | ~ v2_tex_2(B_276,A_275)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | v1_xboole_0(B_276)
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4296,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_4265])).

tff(c_4306,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1043,c_4296])).

tff(c_4307,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_4306])).

tff(c_30,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4332,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4307,c_30])).

tff(c_4354,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_4332])).

tff(c_4355,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1041,c_4354])).

tff(c_4359,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_4355])).

tff(c_4363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3836,c_4359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.21/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/2.07  
% 5.21/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.21/2.07  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.21/2.07  
% 5.21/2.07  %Foreground sorts:
% 5.21/2.07  
% 5.21/2.07  
% 5.21/2.07  %Background operators:
% 5.21/2.07  
% 5.21/2.07  
% 5.21/2.07  %Foreground operators:
% 5.21/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.21/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.21/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.21/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.21/2.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.21/2.07  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.21/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.21/2.07  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.21/2.07  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.21/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.21/2.07  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.21/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.21/2.07  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.21/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.21/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.21/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.21/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.21/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.21/2.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.21/2.07  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.21/2.07  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.21/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.21/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.21/2.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.21/2.07  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.21/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.21/2.07  
% 5.58/2.09  tff(f_212, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.58/2.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.58/2.09  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.58/2.09  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.58/2.09  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.58/2.09  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.58/2.09  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.58/2.09  tff(f_46, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.58/2.09  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.58/2.09  tff(f_151, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.58/2.09  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 5.58/2.09  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 5.58/2.09  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.58/2.09  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.58/2.09  tff(f_138, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 5.58/2.09  tff(f_118, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (((~v2_struct_0(B) & ~v7_struct_0(B)) & v2_tdlat_3(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc23_tex_2)).
% 5.58/2.09  tff(f_75, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.58/2.09  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_62, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.58/2.09  tff(c_18, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.58/2.09  tff(c_72, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_83, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 5.58/2.09  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.58/2.09  tff(c_104, plain, (![A_61, B_62]: (r2_hidden(A_61, B_62) | ~r1_tarski(k1_tarski(A_61), B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.58/2.09  tff(c_109, plain, (![A_61]: (r2_hidden(A_61, k1_tarski(A_61)))), inference(resolution, [status(thm)], [c_10, c_104])).
% 5.58/2.09  tff(c_156, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, C_77) | ~r1_tarski(B_78, C_77) | ~r1_tarski(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.58/2.09  tff(c_267, plain, (![A_89, B_90, A_91]: (r1_tarski(A_89, B_90) | ~r1_tarski(A_89, k1_tarski(A_91)) | ~r2_hidden(A_91, B_90))), inference(resolution, [status(thm)], [c_18, c_156])).
% 5.58/2.09  tff(c_412, plain, (![A_102, B_103, A_104]: (r1_tarski(k1_tarski(A_102), B_103) | ~r2_hidden(A_104, B_103) | ~r2_hidden(A_102, k1_tarski(A_104)))), inference(resolution, [status(thm)], [c_18, c_267])).
% 5.58/2.09  tff(c_439, plain, (![A_109, A_110]: (r1_tarski(k1_tarski(A_109), A_110) | ~r2_hidden(A_109, k1_tarski('#skF_1'(A_110))) | v1_xboole_0(A_110))), inference(resolution, [status(thm)], [c_4, c_412])).
% 5.58/2.09  tff(c_455, plain, (![A_111]: (r1_tarski(k1_tarski('#skF_1'(A_111)), A_111) | v1_xboole_0(A_111))), inference(resolution, [status(thm)], [c_109, c_439])).
% 5.58/2.09  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_127, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.58/2.09  tff(c_140, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_127])).
% 5.58/2.09  tff(c_166, plain, (![A_79]: (r1_tarski(A_79, u1_struct_0('#skF_3')) | ~r1_tarski(A_79, '#skF_4'))), inference(resolution, [status(thm)], [c_140, c_156])).
% 5.58/2.09  tff(c_16, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | ~r1_tarski(k1_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.58/2.09  tff(c_185, plain, (![A_81]: (r2_hidden(A_81, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_81), '#skF_4'))), inference(resolution, [status(thm)], [c_166, c_16])).
% 5.58/2.09  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.58/2.09  tff(c_192, plain, (![A_81]: (m1_subset_1(A_81, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_81), '#skF_4'))), inference(resolution, [status(thm)], [c_185, c_20])).
% 5.58/2.09  tff(c_475, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_455, c_192])).
% 5.58/2.09  tff(c_498, plain, (m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_475])).
% 5.58/2.09  tff(c_14, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.58/2.09  tff(c_78, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_85, plain, (v1_zfmisc_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_83, c_78])).
% 5.58/2.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.58/2.09  tff(c_193, plain, (![A_81]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_81), '#skF_4'))), inference(resolution, [status(thm)], [c_185, c_2])).
% 5.58/2.09  tff(c_194, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_193])).
% 5.58/2.09  tff(c_32, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.58/2.09  tff(c_505, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_498, c_32])).
% 5.58/2.09  tff(c_508, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))=k1_tarski('#skF_1'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_194, c_505])).
% 5.58/2.09  tff(c_299, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(A_95, B_94) | ~v1_zfmisc_1(B_94) | v1_xboole_0(B_94) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.58/2.09  tff(c_311, plain, (![A_11, B_12]: (k1_tarski(A_11)=B_12 | ~v1_zfmisc_1(B_12) | v1_xboole_0(B_12) | v1_xboole_0(k1_tarski(A_11)) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_18, c_299])).
% 5.58/2.09  tff(c_344, plain, (![A_97, B_98]: (k1_tarski(A_97)=B_98 | ~v1_zfmisc_1(B_98) | v1_xboole_0(B_98) | ~r2_hidden(A_97, B_98))), inference(negUnitSimplification, [status(thm)], [c_14, c_311])).
% 5.58/2.09  tff(c_360, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_344])).
% 5.58/2.09  tff(c_450, plain, (![A_110]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_110)))), A_110) | v1_xboole_0(A_110) | v1_xboole_0(k1_tarski('#skF_1'(A_110))))), inference(resolution, [status(thm)], [c_4, c_439])).
% 5.58/2.09  tff(c_521, plain, (![A_112]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_112)))), A_112) | v1_xboole_0(A_112))), inference(negUnitSimplification, [status(thm)], [c_14, c_450])).
% 5.58/2.09  tff(c_541, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_521, c_192])).
% 5.58/2.09  tff(c_568, plain, (m1_subset_1('#skF_1'(k1_tarski('#skF_1'('#skF_4'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_541])).
% 5.58/2.09  tff(c_575, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k1_tarski('#skF_1'('#skF_4'))))=k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4')))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_568, c_32])).
% 5.58/2.09  tff(c_581, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'(k1_tarski('#skF_1'('#skF_4'))))=k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_194, c_575])).
% 5.58/2.09  tff(c_715, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4'))))=k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_360, c_581])).
% 5.58/2.09  tff(c_723, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4'))))=k1_tarski('#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_508, c_715])).
% 5.58/2.09  tff(c_724, plain, (k1_tarski('#skF_1'(k1_tarski('#skF_1'('#skF_4'))))=k1_tarski('#skF_1'('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_723])).
% 5.58/2.09  tff(c_454, plain, (![A_110]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_110)))), A_110) | v1_xboole_0(A_110))), inference(negUnitSimplification, [status(thm)], [c_14, c_450])).
% 5.58/2.09  tff(c_751, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_4')), '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_724, c_454])).
% 5.58/2.09  tff(c_799, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_4')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_751])).
% 5.58/2.09  tff(c_46, plain, (![B_40, A_38]: (B_40=A_38 | ~r1_tarski(A_38, B_40) | ~v1_zfmisc_1(B_40) | v1_xboole_0(B_40) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_151])).
% 5.58/2.09  tff(c_819, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_4')))), inference(resolution, [status(thm)], [c_799, c_46])).
% 5.58/2.09  tff(c_838, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_1'('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_819])).
% 5.58/2.09  tff(c_839, plain, (k1_tarski('#skF_1'('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_14, c_62, c_838])).
% 5.58/2.09  tff(c_851, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_839, c_508])).
% 5.58/2.09  tff(c_58, plain, (![A_47, B_49]: (v2_tex_2(k6_domain_1(u1_struct_0(A_47), B_49), A_47) | ~m1_subset_1(B_49, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_192])).
% 5.58/2.09  tff(c_992, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_1'('#skF_4'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_851, c_58])).
% 5.58/2.09  tff(c_1002, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_498, c_992])).
% 5.58/2.09  tff(c_1004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_83, c_1002])).
% 5.58/2.09  tff(c_1026, plain, (![A_127]: (~r1_tarski(k1_tarski(A_127), '#skF_4'))), inference(splitRight, [status(thm)], [c_193])).
% 5.58/2.09  tff(c_1032, plain, (![A_128]: (~r2_hidden(A_128, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1026])).
% 5.58/2.09  tff(c_1036, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1032])).
% 5.58/2.09  tff(c_1040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1036])).
% 5.58/2.09  tff(c_1041, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_72])).
% 5.58/2.09  tff(c_1043, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1041, c_78])).
% 5.58/2.09  tff(c_3772, plain, (![A_271, B_272]: (m1_pre_topc('#skF_2'(A_271, B_272), A_271) | ~v2_tex_2(B_272, A_271) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | v1_xboole_0(B_272) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.58/2.09  tff(c_3795, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3772])).
% 5.58/2.09  tff(c_3805, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1043, c_3795])).
% 5.58/2.09  tff(c_3806, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_3805])).
% 5.58/2.09  tff(c_28, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.58/2.09  tff(c_3819, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_3806, c_28])).
% 5.58/2.09  tff(c_3836, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3819])).
% 5.58/2.09  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.58/2.09  tff(c_66, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 5.58/2.09  tff(c_44, plain, (![B_37, A_35]: (v2_tdlat_3(B_37) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35) | ~v2_tdlat_3(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.58/2.09  tff(c_3816, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3806, c_44])).
% 5.58/2.09  tff(c_3832, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_3816])).
% 5.58/2.09  tff(c_3833, plain, (v2_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_3832])).
% 5.58/2.09  tff(c_2760, plain, (![A_244, B_245]: (~v2_struct_0('#skF_2'(A_244, B_245)) | ~v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | v1_xboole_0(B_245) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.58/2.09  tff(c_2791, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2760])).
% 5.58/2.09  tff(c_2801, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1043, c_2791])).
% 5.58/2.09  tff(c_2802, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_2801])).
% 5.58/2.09  tff(c_2939, plain, (![A_252, B_253]: (v1_tdlat_3('#skF_2'(A_252, B_253)) | ~v2_tex_2(B_253, A_252) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | v1_xboole_0(B_253) | ~l1_pre_topc(A_252) | ~v2_pre_topc(A_252) | v2_struct_0(A_252))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.58/2.09  tff(c_2970, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_2939])).
% 5.58/2.09  tff(c_2980, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1043, c_2970])).
% 5.58/2.09  tff(c_2981, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_2980])).
% 5.58/2.09  tff(c_38, plain, (![B_33, A_31]: (~v1_tdlat_3(B_33) | ~v2_tdlat_3(B_33) | v7_struct_0(B_33) | v2_struct_0(B_33) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.58/2.09  tff(c_3813, plain, (~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3806, c_38])).
% 5.58/2.09  tff(c_3828, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2981, c_3813])).
% 5.58/2.09  tff(c_3829, plain, (~v2_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_2802, c_3828])).
% 5.58/2.09  tff(c_3842, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3833, c_3829])).
% 5.58/2.09  tff(c_4265, plain, (![A_275, B_276]: (u1_struct_0('#skF_2'(A_275, B_276))=B_276 | ~v2_tex_2(B_276, A_275) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | v1_xboole_0(B_276) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.58/2.09  tff(c_4296, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_4265])).
% 5.58/2.09  tff(c_4306, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1043, c_4296])).
% 5.58/2.09  tff(c_4307, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_4306])).
% 5.58/2.09  tff(c_30, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.58/2.09  tff(c_4332, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4307, c_30])).
% 5.58/2.09  tff(c_4354, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_4332])).
% 5.58/2.09  tff(c_4355, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1041, c_4354])).
% 5.58/2.09  tff(c_4359, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_4355])).
% 5.58/2.09  tff(c_4363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3836, c_4359])).
% 5.58/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.58/2.09  
% 5.58/2.09  Inference rules
% 5.58/2.09  ----------------------
% 5.58/2.09  #Ref     : 0
% 5.58/2.09  #Sup     : 990
% 5.58/2.09  #Fact    : 0
% 5.58/2.09  #Define  : 0
% 5.58/2.09  #Split   : 11
% 5.58/2.09  #Chain   : 0
% 5.58/2.09  #Close   : 0
% 5.58/2.09  
% 5.58/2.09  Ordering : KBO
% 5.58/2.09  
% 5.58/2.09  Simplification rules
% 5.58/2.09  ----------------------
% 5.58/2.09  #Subsume      : 255
% 5.58/2.09  #Demod        : 206
% 5.58/2.09  #Tautology    : 211
% 5.58/2.09  #SimpNegUnit  : 265
% 5.58/2.09  #BackRed      : 4
% 5.58/2.09  
% 5.58/2.09  #Partial instantiations: 0
% 5.58/2.09  #Strategies tried      : 1
% 5.58/2.09  
% 5.58/2.09  Timing (in seconds)
% 5.58/2.09  ----------------------
% 5.58/2.10  Preprocessing        : 0.36
% 5.58/2.10  Parsing              : 0.20
% 5.58/2.10  CNF conversion       : 0.03
% 5.58/2.10  Main loop            : 0.87
% 5.58/2.10  Inferencing          : 0.29
% 5.58/2.10  Reduction            : 0.28
% 5.58/2.10  Demodulation         : 0.18
% 5.58/2.10  BG Simplification    : 0.04
% 5.58/2.10  Subsumption          : 0.19
% 5.58/2.10  Abstraction          : 0.05
% 5.58/2.10  MUC search           : 0.00
% 5.58/2.10  Cooper               : 0.00
% 5.58/2.10  Total                : 1.28
% 5.58/2.10  Index Insertion      : 0.00
% 5.58/2.10  Index Deletion       : 0.00
% 5.58/2.10  Index Matching       : 0.00
% 5.58/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
