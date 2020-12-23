%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:56 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 788 expanded)
%              Number of leaves         :   42 ( 282 expanded)
%              Depth                    :   24
%              Number of atoms          :  307 (2430 expanded)
%              Number of equality atoms :   25 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
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

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_154,axiom,(
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

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_76,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_78,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_44,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_3'(A_27),A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_107,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_183,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_204,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77),B_78)
      | ~ r1_tarski(A_77,B_78)
      | v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_183])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [B_81,A_82] :
      ( ~ v1_xboole_0(B_81)
      | ~ r1_tarski(A_82,B_81)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_204,c_2])).

tff(c_255,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_115,c_243])).

tff(c_261,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_255])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_444,plain,(
    ! [A_109,B_110,B_111] :
      ( r2_hidden(A_109,B_110)
      | ~ r1_tarski(B_111,B_110)
      | v1_xboole_0(B_111)
      | ~ m1_subset_1(A_109,B_111) ) ),
    inference(resolution,[status(thm)],[c_20,c_183])).

tff(c_456,plain,(
    ! [A_109] :
      ( r2_hidden(A_109,u1_struct_0('#skF_5'))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_109,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_115,c_444])).

tff(c_465,plain,(
    ! [A_112] :
      ( r2_hidden(A_112,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_112,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_456])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_474,plain,(
    ! [A_112] :
      ( m1_subset_1(A_112,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_112,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_465,c_12])).

tff(c_484,plain,(
    ! [A_113] :
      ( m1_subset_1(A_113,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_113,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_474])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( k6_domain_1(A_21,B_22) = k1_tarski(B_22)
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_494,plain,(
    ! [A_113] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_113) = k1_tarski(A_113)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_113,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_484,c_32])).

tff(c_506,plain,(
    ! [A_113] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_113) = k1_tarski(A_113)
      | ~ m1_subset_1(A_113,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_494])).

tff(c_40,plain,(
    ! [A_27,B_30] :
      ( v1_zfmisc_1(A_27)
      | k6_domain_1(A_27,B_30) != A_27
      | ~ m1_subset_1(B_30,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_491,plain,(
    ! [A_113] :
      ( v1_zfmisc_1(u1_struct_0('#skF_5'))
      | k6_domain_1(u1_struct_0('#skF_5'),A_113) != u1_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_113,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_484,c_40])).

tff(c_503,plain,(
    ! [A_113] :
      ( v1_zfmisc_1(u1_struct_0('#skF_5'))
      | k6_domain_1(u1_struct_0('#skF_5'),A_113) != u1_struct_0('#skF_5')
      | ~ m1_subset_1(A_113,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_491])).

tff(c_779,plain,(
    ! [A_127] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_127) != u1_struct_0('#skF_5')
      | ~ m1_subset_1(A_127,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_844,plain,(
    ! [A_130] :
      ( u1_struct_0('#skF_5') != k1_tarski(A_130)
      | ~ m1_subset_1(A_130,'#skF_6')
      | ~ m1_subset_1(A_130,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_779])).

tff(c_853,plain,
    ( k1_tarski('#skF_3'('#skF_6')) != u1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_844])).

tff(c_868,plain,
    ( k1_tarski('#skF_3'('#skF_6')) != u1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_853])).

tff(c_869,plain,
    ( k1_tarski('#skF_3'('#skF_6')) != u1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_868])).

tff(c_891,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_915,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_891])).

tff(c_921,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_915])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_921])).

tff(c_925,plain,(
    m1_subset_1('#skF_3'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_482,plain,(
    ! [A_112] :
      ( m1_subset_1(A_112,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_112,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_474])).

tff(c_70,plain,
    ( ~ v1_zfmisc_1('#skF_6')
    | ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_81,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_70])).

tff(c_954,plain,
    ( k6_domain_1('#skF_6','#skF_3'('#skF_6')) = k1_tarski('#skF_3'('#skF_6'))
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_925,c_32])).

tff(c_966,plain,(
    k6_domain_1('#skF_6','#skF_3'('#skF_6')) = k1_tarski('#skF_3'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_954])).

tff(c_42,plain,(
    ! [A_27] :
      ( k6_domain_1(A_27,'#skF_3'(A_27)) = A_27
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1037,plain,
    ( k1_tarski('#skF_3'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_42])).

tff(c_1051,plain,
    ( k1_tarski('#skF_3'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1037])).

tff(c_1052,plain,(
    k1_tarski('#skF_3'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1051])).

tff(c_508,plain,(
    ! [A_114] :
      ( k6_domain_1(u1_struct_0('#skF_5'),A_114) = k1_tarski(A_114)
      | ~ m1_subset_1(A_114,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_494])).

tff(c_56,plain,(
    ! [A_37,B_39] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_37),B_39),A_37)
      | ~ m1_subset_1(B_39,u1_struct_0(A_37))
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_518,plain,(
    ! [A_114] :
      ( v2_tex_2(k1_tarski(A_114),'#skF_5')
      | ~ m1_subset_1(A_114,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(A_114,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_56])).

tff(c_550,plain,(
    ! [A_114] :
      ( v2_tex_2(k1_tarski(A_114),'#skF_5')
      | ~ m1_subset_1(A_114,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(A_114,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_518])).

tff(c_551,plain,(
    ! [A_114] :
      ( v2_tex_2(k1_tarski(A_114),'#skF_5')
      | ~ m1_subset_1(A_114,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_114,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_550])).

tff(c_1069,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1052,c_551])).

tff(c_1080,plain,
    ( v2_tex_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_1069])).

tff(c_1081,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_1080])).

tff(c_1151,plain,(
    ~ m1_subset_1('#skF_3'('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_482,c_1081])).

tff(c_1158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_1151])).

tff(c_1159,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1875,plain,(
    ! [A_221,B_222] :
      ( m1_pre_topc('#skF_4'(A_221,B_222),A_221)
      | ~ v2_tex_2(B_222,A_221)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | v1_xboole_0(B_222)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1895,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1875])).

tff(c_1904,plain,
    ( m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1159,c_1895])).

tff(c_1905,plain,(
    m1_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_1904])).

tff(c_28,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1911,plain,
    ( l1_pre_topc('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1905,c_28])).

tff(c_1918,plain,(
    l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1911])).

tff(c_26,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1160,plain,(
    ~ v1_zfmisc_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1755,plain,(
    ! [A_217,B_218] :
      ( ~ v2_struct_0('#skF_4'(A_217,B_218))
      | ~ v2_tex_2(B_218,A_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | v1_xboole_0(B_218)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1782,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1755])).

tff(c_1791,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1159,c_1782])).

tff(c_1792,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_1791])).

tff(c_64,plain,(
    v2_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1665,plain,(
    ! [A_211,B_212] :
      ( v1_tdlat_3('#skF_4'(A_211,B_212))
      | ~ v2_tex_2(B_212,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | v1_xboole_0(B_212)
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1688,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1665])).

tff(c_1696,plain,
    ( v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1159,c_1688])).

tff(c_1697,plain,(
    v1_tdlat_3('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_1696])).

tff(c_36,plain,(
    ! [B_26,A_24] :
      ( ~ v1_tdlat_3(B_26)
      | v7_struct_0(B_26)
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1908,plain,
    ( ~ v1_tdlat_3('#skF_4'('#skF_5','#skF_6'))
    | v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_tdlat_3('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1905,c_36])).

tff(c_1914,plain,
    ( v7_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_4'('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1697,c_1908])).

tff(c_1915,plain,(
    v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1792,c_1914])).

tff(c_2003,plain,(
    ! [A_225,B_226] :
      ( u1_struct_0('#skF_4'(A_225,B_226)) = B_226
      | ~ v2_tex_2(B_226,A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | v1_xboole_0(B_226)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2030,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | ~ v2_tex_2('#skF_6','#skF_5')
    | v1_xboole_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2003])).

tff(c_2039,plain,
    ( u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1159,c_2030])).

tff(c_2040,plain,(
    u1_struct_0('#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_60,c_2039])).

tff(c_30,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | ~ v7_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2061,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v7_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2040,c_30])).

tff(c_2083,plain,
    ( v1_zfmisc_1('#skF_6')
    | ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_2061])).

tff(c_2084,plain,(
    ~ l1_struct_0('#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1160,c_2083])).

tff(c_2088,plain,(
    ~ l1_pre_topc('#skF_4'('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_26,c_2084])).

tff(c_2092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_2088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n010.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 14:46:29 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.63  
% 4.00/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.63  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.00/1.63  
% 4.00/1.63  %Foreground sorts:
% 4.00/1.63  
% 4.00/1.63  
% 4.00/1.63  %Background operators:
% 4.00/1.63  
% 4.00/1.63  
% 4.00/1.63  %Foreground operators:
% 4.00/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.00/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.00/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.00/1.63  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 4.00/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.00/1.63  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.00/1.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.00/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.63  tff('#skF_5', type, '#skF_5': $i).
% 4.00/1.63  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.00/1.63  tff('#skF_6', type, '#skF_6': $i).
% 4.00/1.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.00/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.00/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.63  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.00/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.00/1.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.00/1.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.00/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.00/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.00/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.00/1.63  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.00/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/1.63  
% 4.00/1.65  tff(f_186, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 4.00/1.65  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 4.00/1.65  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.00/1.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.00/1.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.00/1.65  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.00/1.65  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.00/1.65  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.00/1.65  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 4.00/1.65  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tex_2)).
% 4.00/1.65  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.00/1.65  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.00/1.65  tff(f_115, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 4.00/1.65  tff(f_78, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 4.00/1.65  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_60, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_76, plain, (v2_tex_2('#skF_6', '#skF_5') | v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_78, plain, (v1_zfmisc_1('#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 4.00/1.65  tff(c_44, plain, (![A_27]: (m1_subset_1('#skF_3'(A_27), A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.00/1.65  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_107, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.00/1.65  tff(c_115, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_107])).
% 4.00/1.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.65  tff(c_183, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.00/1.65  tff(c_204, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77), B_78) | ~r1_tarski(A_77, B_78) | v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_4, c_183])).
% 4.00/1.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.00/1.65  tff(c_243, plain, (![B_81, A_82]: (~v1_xboole_0(B_81) | ~r1_tarski(A_82, B_81) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_204, c_2])).
% 4.00/1.65  tff(c_255, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_115, c_243])).
% 4.00/1.65  tff(c_261, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_255])).
% 4.00/1.65  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.65  tff(c_444, plain, (![A_109, B_110, B_111]: (r2_hidden(A_109, B_110) | ~r1_tarski(B_111, B_110) | v1_xboole_0(B_111) | ~m1_subset_1(A_109, B_111))), inference(resolution, [status(thm)], [c_20, c_183])).
% 4.00/1.65  tff(c_456, plain, (![A_109]: (r2_hidden(A_109, u1_struct_0('#skF_5')) | v1_xboole_0('#skF_6') | ~m1_subset_1(A_109, '#skF_6'))), inference(resolution, [status(thm)], [c_115, c_444])).
% 4.00/1.65  tff(c_465, plain, (![A_112]: (r2_hidden(A_112, u1_struct_0('#skF_5')) | ~m1_subset_1(A_112, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_456])).
% 4.00/1.65  tff(c_12, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.00/1.65  tff(c_474, plain, (![A_112]: (m1_subset_1(A_112, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_112, '#skF_6'))), inference(resolution, [status(thm)], [c_465, c_12])).
% 4.00/1.65  tff(c_484, plain, (![A_113]: (m1_subset_1(A_113, u1_struct_0('#skF_5')) | ~m1_subset_1(A_113, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_261, c_474])).
% 4.00/1.65  tff(c_32, plain, (![A_21, B_22]: (k6_domain_1(A_21, B_22)=k1_tarski(B_22) | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.00/1.65  tff(c_494, plain, (![A_113]: (k6_domain_1(u1_struct_0('#skF_5'), A_113)=k1_tarski(A_113) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_113, '#skF_6'))), inference(resolution, [status(thm)], [c_484, c_32])).
% 4.00/1.65  tff(c_506, plain, (![A_113]: (k6_domain_1(u1_struct_0('#skF_5'), A_113)=k1_tarski(A_113) | ~m1_subset_1(A_113, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_261, c_494])).
% 4.00/1.65  tff(c_40, plain, (![A_27, B_30]: (v1_zfmisc_1(A_27) | k6_domain_1(A_27, B_30)!=A_27 | ~m1_subset_1(B_30, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.00/1.65  tff(c_491, plain, (![A_113]: (v1_zfmisc_1(u1_struct_0('#skF_5')) | k6_domain_1(u1_struct_0('#skF_5'), A_113)!=u1_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_113, '#skF_6'))), inference(resolution, [status(thm)], [c_484, c_40])).
% 4.00/1.65  tff(c_503, plain, (![A_113]: (v1_zfmisc_1(u1_struct_0('#skF_5')) | k6_domain_1(u1_struct_0('#skF_5'), A_113)!=u1_struct_0('#skF_5') | ~m1_subset_1(A_113, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_261, c_491])).
% 4.00/1.65  tff(c_779, plain, (![A_127]: (k6_domain_1(u1_struct_0('#skF_5'), A_127)!=u1_struct_0('#skF_5') | ~m1_subset_1(A_127, '#skF_6'))), inference(splitLeft, [status(thm)], [c_503])).
% 4.00/1.65  tff(c_844, plain, (![A_130]: (u1_struct_0('#skF_5')!=k1_tarski(A_130) | ~m1_subset_1(A_130, '#skF_6') | ~m1_subset_1(A_130, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_506, c_779])).
% 4.00/1.65  tff(c_853, plain, (k1_tarski('#skF_3'('#skF_6'))!=u1_struct_0('#skF_5') | ~m1_subset_1('#skF_3'('#skF_6'), '#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_844])).
% 4.00/1.65  tff(c_868, plain, (k1_tarski('#skF_3'('#skF_6'))!=u1_struct_0('#skF_5') | ~m1_subset_1('#skF_3'('#skF_6'), '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_853])).
% 4.00/1.65  tff(c_869, plain, (k1_tarski('#skF_3'('#skF_6'))!=u1_struct_0('#skF_5') | ~m1_subset_1('#skF_3'('#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_868])).
% 4.00/1.65  tff(c_891, plain, (~m1_subset_1('#skF_3'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_869])).
% 4.00/1.65  tff(c_915, plain, (~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_891])).
% 4.00/1.65  tff(c_921, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_915])).
% 4.00/1.65  tff(c_923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_921])).
% 4.00/1.65  tff(c_925, plain, (m1_subset_1('#skF_3'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_869])).
% 4.00/1.65  tff(c_482, plain, (![A_112]: (m1_subset_1(A_112, u1_struct_0('#skF_5')) | ~m1_subset_1(A_112, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_261, c_474])).
% 4.00/1.65  tff(c_70, plain, (~v1_zfmisc_1('#skF_6') | ~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_81, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_70])).
% 4.00/1.65  tff(c_954, plain, (k6_domain_1('#skF_6', '#skF_3'('#skF_6'))=k1_tarski('#skF_3'('#skF_6')) | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_925, c_32])).
% 4.00/1.65  tff(c_966, plain, (k6_domain_1('#skF_6', '#skF_3'('#skF_6'))=k1_tarski('#skF_3'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_954])).
% 4.00/1.65  tff(c_42, plain, (![A_27]: (k6_domain_1(A_27, '#skF_3'(A_27))=A_27 | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.00/1.65  tff(c_1037, plain, (k1_tarski('#skF_3'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_966, c_42])).
% 4.00/1.65  tff(c_1051, plain, (k1_tarski('#skF_3'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1037])).
% 4.00/1.65  tff(c_1052, plain, (k1_tarski('#skF_3'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_60, c_1051])).
% 4.00/1.65  tff(c_508, plain, (![A_114]: (k6_domain_1(u1_struct_0('#skF_5'), A_114)=k1_tarski(A_114) | ~m1_subset_1(A_114, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_261, c_494])).
% 4.00/1.65  tff(c_56, plain, (![A_37, B_39]: (v2_tex_2(k6_domain_1(u1_struct_0(A_37), B_39), A_37) | ~m1_subset_1(B_39, u1_struct_0(A_37)) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_166])).
% 4.00/1.65  tff(c_518, plain, (![A_114]: (v2_tex_2(k1_tarski(A_114), '#skF_5') | ~m1_subset_1(A_114, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(A_114, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_508, c_56])).
% 4.00/1.65  tff(c_550, plain, (![A_114]: (v2_tex_2(k1_tarski(A_114), '#skF_5') | ~m1_subset_1(A_114, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(A_114, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_518])).
% 4.00/1.65  tff(c_551, plain, (![A_114]: (v2_tex_2(k1_tarski(A_114), '#skF_5') | ~m1_subset_1(A_114, u1_struct_0('#skF_5')) | ~m1_subset_1(A_114, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_550])).
% 4.00/1.65  tff(c_1069, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_3'('#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'('#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1052, c_551])).
% 4.00/1.65  tff(c_1080, plain, (v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_3'('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_925, c_1069])).
% 4.00/1.65  tff(c_1081, plain, (~m1_subset_1('#skF_3'('#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_81, c_1080])).
% 4.00/1.65  tff(c_1151, plain, (~m1_subset_1('#skF_3'('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_482, c_1081])).
% 4.00/1.65  tff(c_1158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_1151])).
% 4.00/1.65  tff(c_1159, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 4.00/1.65  tff(c_1875, plain, (![A_221, B_222]: (m1_pre_topc('#skF_4'(A_221, B_222), A_221) | ~v2_tex_2(B_222, A_221) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | v1_xboole_0(B_222) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.00/1.65  tff(c_1895, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1875])).
% 4.00/1.65  tff(c_1904, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1159, c_1895])).
% 4.00/1.65  tff(c_1905, plain, (m1_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_1904])).
% 4.00/1.65  tff(c_28, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.00/1.65  tff(c_1911, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1905, c_28])).
% 4.00/1.65  tff(c_1918, plain, (l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1911])).
% 4.00/1.65  tff(c_26, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.00/1.65  tff(c_1160, plain, (~v1_zfmisc_1('#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 4.00/1.65  tff(c_1755, plain, (![A_217, B_218]: (~v2_struct_0('#skF_4'(A_217, B_218)) | ~v2_tex_2(B_218, A_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | v1_xboole_0(B_218) | ~l1_pre_topc(A_217) | ~v2_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.00/1.65  tff(c_1782, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1755])).
% 4.00/1.65  tff(c_1791, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1159, c_1782])).
% 4.00/1.65  tff(c_1792, plain, (~v2_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_1791])).
% 4.00/1.65  tff(c_64, plain, (v2_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_186])).
% 4.00/1.65  tff(c_1665, plain, (![A_211, B_212]: (v1_tdlat_3('#skF_4'(A_211, B_212)) | ~v2_tex_2(B_212, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0(A_211))) | v1_xboole_0(B_212) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211) | v2_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.00/1.65  tff(c_1688, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1665])).
% 4.00/1.65  tff(c_1696, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1159, c_1688])).
% 4.00/1.65  tff(c_1697, plain, (v1_tdlat_3('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_1696])).
% 4.00/1.65  tff(c_36, plain, (![B_26, A_24]: (~v1_tdlat_3(B_26) | v7_struct_0(B_26) | v2_struct_0(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.00/1.65  tff(c_1908, plain, (~v1_tdlat_3('#skF_4'('#skF_5', '#skF_6')) | v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_tdlat_3('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1905, c_36])).
% 4.00/1.65  tff(c_1914, plain, (v7_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_4'('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1697, c_1908])).
% 4.00/1.65  tff(c_1915, plain, (v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1792, c_1914])).
% 4.00/1.65  tff(c_2003, plain, (![A_225, B_226]: (u1_struct_0('#skF_4'(A_225, B_226))=B_226 | ~v2_tex_2(B_226, A_225) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | v1_xboole_0(B_226) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.00/1.65  tff(c_2030, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | ~v2_tex_2('#skF_6', '#skF_5') | v1_xboole_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2003])).
% 4.00/1.65  tff(c_2039, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6' | v1_xboole_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1159, c_2030])).
% 4.00/1.65  tff(c_2040, plain, (u1_struct_0('#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_68, c_60, c_2039])).
% 4.00/1.65  tff(c_30, plain, (![A_20]: (v1_zfmisc_1(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | ~v7_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.00/1.65  tff(c_2061, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6')) | ~v7_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2040, c_30])).
% 4.00/1.65  tff(c_2083, plain, (v1_zfmisc_1('#skF_6') | ~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_2061])).
% 4.00/1.65  tff(c_2084, plain, (~l1_struct_0('#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1160, c_2083])).
% 4.00/1.65  tff(c_2088, plain, (~l1_pre_topc('#skF_4'('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_26, c_2084])).
% 4.00/1.65  tff(c_2092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1918, c_2088])).
% 4.00/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.65  
% 4.00/1.65  Inference rules
% 4.00/1.65  ----------------------
% 4.00/1.65  #Ref     : 0
% 4.00/1.65  #Sup     : 408
% 4.00/1.65  #Fact    : 0
% 4.00/1.65  #Define  : 0
% 4.00/1.65  #Split   : 13
% 4.00/1.65  #Chain   : 0
% 4.00/1.65  #Close   : 0
% 4.00/1.65  
% 4.00/1.65  Ordering : KBO
% 4.00/1.65  
% 4.00/1.65  Simplification rules
% 4.00/1.65  ----------------------
% 4.00/1.65  #Subsume      : 57
% 4.00/1.65  #Demod        : 91
% 4.00/1.65  #Tautology    : 130
% 4.00/1.65  #SimpNegUnit  : 109
% 4.00/1.65  #BackRed      : 3
% 4.00/1.65  
% 4.00/1.65  #Partial instantiations: 0
% 4.00/1.65  #Strategies tried      : 1
% 4.00/1.65  
% 4.00/1.65  Timing (in seconds)
% 4.00/1.65  ----------------------
% 4.00/1.65  Preprocessing        : 0.35
% 4.00/1.65  Parsing              : 0.19
% 4.00/1.65  CNF conversion       : 0.02
% 4.00/1.65  Main loop            : 0.56
% 4.00/1.65  Inferencing          : 0.21
% 4.00/1.65  Reduction            : 0.16
% 4.00/1.65  Demodulation         : 0.10
% 4.00/1.66  BG Simplification    : 0.03
% 4.00/1.66  Subsumption          : 0.11
% 4.00/1.66  Abstraction          : 0.03
% 4.00/1.66  MUC search           : 0.00
% 4.00/1.66  Cooper               : 0.00
% 4.00/1.66  Total                : 0.95
% 4.00/1.66  Index Insertion      : 0.00
% 4.00/1.66  Index Deletion       : 0.00
% 4.00/1.66  Index Matching       : 0.00
% 4.00/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
