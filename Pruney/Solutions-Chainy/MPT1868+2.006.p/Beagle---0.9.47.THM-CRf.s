%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  125 (1240 expanded)
%              Number of leaves         :   40 ( 425 expanded)
%              Depth                    :   20
%              Number of atoms          :  310 (3554 expanded)
%              Number of equality atoms :   43 ( 304 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_62,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_117,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_121,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_189,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_189])).

tff(c_209,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_201])).

tff(c_58,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_219,plain,(
    ~ v2_tex_2(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_58])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [B_49,A_50] :
      ( ~ r2_hidden(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k6_domain_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_223,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_34])).

tff(c_227,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_223])).

tff(c_228,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_227])).

tff(c_576,plain,(
    ! [A_105,B_106] :
      ( ~ v2_struct_0('#skF_4'(A_105,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | v1_xboole_0(B_106)
      | ~ l1_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_587,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_576])).

tff(c_606,plain,
    ( ~ v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_587])).

tff(c_607,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_606])).

tff(c_470,plain,(
    ! [A_98,B_99] :
      ( v1_pre_topc('#skF_4'(A_98,B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | v1_xboole_0(B_99)
      | ~ l1_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_477,plain,
    ( v1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_470])).

tff(c_493,plain,
    ( v1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_477])).

tff(c_494,plain,(
    v1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_493])).

tff(c_1189,plain,(
    ! [A_157,B_158] :
      ( u1_struct_0('#skF_4'(A_157,B_158)) = B_158
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_157)))
      | v1_xboole_0(B_158)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1204,plain,
    ( u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_1189])).

tff(c_1224,plain,
    ( u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1204])).

tff(c_1225,plain,(
    u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_1224])).

tff(c_1229,plain,(
    ! [A_159,B_160] :
      ( m1_pre_topc('#skF_4'(A_159,B_160),A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | v1_xboole_0(B_160)
      | ~ l1_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1240,plain,
    ( m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_1229])).

tff(c_1257,plain,
    ( m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1240])).

tff(c_1258,plain,(
    m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_1257])).

tff(c_1550,plain,(
    ! [A_190,B_191,C_192] :
      ( k1_tex_2(A_190,B_191) = C_192
      | u1_struct_0(C_192) != k6_domain_1(u1_struct_0(A_190),B_191)
      | ~ m1_pre_topc(C_192,A_190)
      | ~ v1_pre_topc(C_192)
      | v2_struct_0(C_192)
      | ~ m1_subset_1(B_191,u1_struct_0(A_190))
      | ~ l1_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1562,plain,(
    ! [C_192] :
      ( k1_tex_2('#skF_5','#skF_6') = C_192
      | u1_struct_0(C_192) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_192,'#skF_5')
      | ~ v1_pre_topc(C_192)
      | v2_struct_0(C_192)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1550])).

tff(c_1569,plain,(
    ! [C_192] :
      ( k1_tex_2('#skF_5','#skF_6') = C_192
      | u1_struct_0(C_192) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_192,'#skF_5')
      | ~ v1_pre_topc(C_192)
      | v2_struct_0(C_192)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1562])).

tff(c_1571,plain,(
    ! [C_193] :
      ( k1_tex_2('#skF_5','#skF_6') = C_193
      | u1_struct_0(C_193) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_193,'#skF_5')
      | ~ v1_pre_topc(C_193)
      | v2_struct_0(C_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1569])).

tff(c_1574,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6')
    | u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) != k1_tarski('#skF_6')
    | ~ v1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1258,c_1571])).

tff(c_1577,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6')
    | v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_1225,c_1574])).

tff(c_1578,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_1577])).

tff(c_1582,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1258])).

tff(c_1583,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_607])).

tff(c_611,plain,(
    ! [A_107,B_108] :
      ( v1_tdlat_3(k1_tex_2(A_107,B_108))
      | ~ v2_pre_topc(k1_tex_2(A_107,B_108))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_626,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_5','#skF_6'))
    | ~ v2_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_611])).

tff(c_632,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_5','#skF_6'))
    | ~ v2_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_626])).

tff(c_633,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_5','#skF_6'))
    | ~ v2_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_632])).

tff(c_634,plain,(
    ~ v2_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_633])).

tff(c_755,plain,(
    ! [A_117,B_118] :
      ( u1_struct_0('#skF_4'(A_117,B_118)) = B_118
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | v1_xboole_0(B_118)
      | ~ l1_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_770,plain,
    ( u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_755])).

tff(c_790,plain,
    ( u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_770])).

tff(c_791,plain,(
    u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_790])).

tff(c_716,plain,(
    ! [A_115,B_116] :
      ( m1_pre_topc('#skF_4'(A_115,B_116),A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | v1_xboole_0(B_116)
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_727,plain,
    ( m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_716])).

tff(c_744,plain,
    ( m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_727])).

tff(c_745,plain,(
    m1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_82,c_744])).

tff(c_1080,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_tex_2(A_147,B_148) = C_149
      | u1_struct_0(C_149) != k6_domain_1(u1_struct_0(A_147),B_148)
      | ~ m1_pre_topc(C_149,A_147)
      | ~ v1_pre_topc(C_149)
      | v2_struct_0(C_149)
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1092,plain,(
    ! [C_149] :
      ( k1_tex_2('#skF_5','#skF_6') = C_149
      | u1_struct_0(C_149) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_149,'#skF_5')
      | ~ v1_pre_topc(C_149)
      | v2_struct_0(C_149)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_1080])).

tff(c_1099,plain,(
    ! [C_149] :
      ( k1_tex_2('#skF_5','#skF_6') = C_149
      | u1_struct_0(C_149) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_149,'#skF_5')
      | ~ v1_pre_topc(C_149)
      | v2_struct_0(C_149)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1092])).

tff(c_1101,plain,(
    ! [C_150] :
      ( k1_tex_2('#skF_5','#skF_6') = C_150
      | u1_struct_0(C_150) != k1_tarski('#skF_6')
      | ~ m1_pre_topc(C_150,'#skF_5')
      | ~ v1_pre_topc(C_150)
      | v2_struct_0(C_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1099])).

tff(c_1104,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6')
    | u1_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) != k1_tarski('#skF_6')
    | ~ v1_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_745,c_1101])).

tff(c_1107,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6')
    | v2_struct_0('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_791,c_1104])).

tff(c_1108,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_6')) = k1_tex_2('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_1107])).

tff(c_64,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_28,plain,(
    ! [B_15,A_13] :
      ( v2_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_751,plain,
    ( v2_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_745,c_28])).

tff(c_754,plain,(
    v2_pre_topc('#skF_4'('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_751])).

tff(c_1111,plain,(
    v2_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_754])).

tff(c_1116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_634,c_1111])).

tff(c_1117,plain,(
    v1_tdlat_3(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_633])).

tff(c_1580,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1225])).

tff(c_54,plain,(
    ! [B_42,A_38] :
      ( v2_tex_2(u1_struct_0(B_42),A_38)
      | ~ v1_tdlat_3(B_42)
      | ~ m1_subset_1(u1_struct_0(B_42),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_42,A_38)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1621,plain,(
    ! [A_38] :
      ( v2_tex_2(u1_struct_0(k1_tex_2('#skF_5','#skF_6')),A_38)
      | ~ v1_tdlat_3(k1_tex_2('#skF_5','#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),A_38)
      | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1580,c_54])).

tff(c_1664,plain,(
    ! [A_38] :
      ( v2_tex_2(k1_tarski('#skF_6'),A_38)
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),A_38)
      | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
      | ~ l1_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_1580,c_1621])).

tff(c_1678,plain,(
    ! [A_194] :
      ( v2_tex_2(k1_tarski('#skF_6'),A_194)
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),A_194)
      | ~ l1_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1583,c_1664])).

tff(c_1684,plain,
    ( v2_tex_2(k1_tarski('#skF_6'),'#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_228,c_1678])).

tff(c_1693,plain,
    ( v2_tex_2(k1_tarski('#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1582,c_1684])).

tff(c_1695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_219,c_1693])).

tff(c_1697,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_32,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1711,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1697,c_32])).

tff(c_1714,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1711])).

tff(c_1717,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_1714])).

tff(c_1721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.79  
% 4.52/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.79  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.52/1.79  
% 4.52/1.79  %Foreground sorts:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Background operators:
% 4.52/1.79  
% 4.52/1.79  
% 4.52/1.79  %Foreground operators:
% 4.52/1.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.52/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.52/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.52/1.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.52/1.79  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 4.52/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.52/1.79  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.52/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.52/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.52/1.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.52/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.52/1.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.52/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.52/1.79  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.79  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 4.52/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.52/1.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.52/1.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.52/1.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.52/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.52/1.79  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.52/1.79  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.52/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.52/1.79  
% 4.69/1.83  tff(f_176, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 4.69/1.83  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.69/1.83  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.69/1.83  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.69/1.83  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.69/1.83  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.69/1.83  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.69/1.83  tff(f_129, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 4.69/1.83  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 4.69/1.83  tff(f_143, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tex_2)).
% 4.69/1.83  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.69/1.83  tff(f_163, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 4.69/1.83  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.69/1.83  tff(c_62, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.69/1.83  tff(c_30, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.69/1.83  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.69/1.83  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.69/1.83  tff(c_117, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.83  tff(c_121, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_117])).
% 4.69/1.83  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_121])).
% 4.69/1.83  tff(c_189, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.69/1.83  tff(c_201, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_189])).
% 4.69/1.83  tff(c_209, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_127, c_201])).
% 4.69/1.83  tff(c_58, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.69/1.83  tff(c_219, plain, (~v2_tex_2(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_58])).
% 4.69/1.83  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.69/1.83  tff(c_78, plain, (![B_49, A_50]: (~r2_hidden(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.83  tff(c_82, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_78])).
% 4.69/1.83  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(k6_domain_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.69/1.83  tff(c_223, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_34])).
% 4.69/1.83  tff(c_227, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_223])).
% 4.69/1.83  tff(c_228, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_127, c_227])).
% 4.69/1.83  tff(c_576, plain, (![A_105, B_106]: (~v2_struct_0('#skF_4'(A_105, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | v1_xboole_0(B_106) | ~l1_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_587, plain, (~v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_576])).
% 4.69/1.83  tff(c_606, plain, (~v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_587])).
% 4.69/1.83  tff(c_607, plain, (~v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_606])).
% 4.69/1.83  tff(c_470, plain, (![A_98, B_99]: (v1_pre_topc('#skF_4'(A_98, B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | v1_xboole_0(B_99) | ~l1_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_477, plain, (v1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_470])).
% 4.69/1.83  tff(c_493, plain, (v1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_477])).
% 4.69/1.83  tff(c_494, plain, (v1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_493])).
% 4.69/1.83  tff(c_1189, plain, (![A_157, B_158]: (u1_struct_0('#skF_4'(A_157, B_158))=B_158 | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_157))) | v1_xboole_0(B_158) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_1204, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_1189])).
% 4.69/1.83  tff(c_1224, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1204])).
% 4.69/1.83  tff(c_1225, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_1224])).
% 4.69/1.83  tff(c_1229, plain, (![A_159, B_160]: (m1_pre_topc('#skF_4'(A_159, B_160), A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | v1_xboole_0(B_160) | ~l1_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_1240, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_1229])).
% 4.69/1.83  tff(c_1257, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1240])).
% 4.69/1.83  tff(c_1258, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_1257])).
% 4.69/1.83  tff(c_1550, plain, (![A_190, B_191, C_192]: (k1_tex_2(A_190, B_191)=C_192 | u1_struct_0(C_192)!=k6_domain_1(u1_struct_0(A_190), B_191) | ~m1_pre_topc(C_192, A_190) | ~v1_pre_topc(C_192) | v2_struct_0(C_192) | ~m1_subset_1(B_191, u1_struct_0(A_190)) | ~l1_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.69/1.83  tff(c_1562, plain, (![C_192]: (k1_tex_2('#skF_5', '#skF_6')=C_192 | u1_struct_0(C_192)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_192, '#skF_5') | ~v1_pre_topc(C_192) | v2_struct_0(C_192) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1550])).
% 4.69/1.83  tff(c_1569, plain, (![C_192]: (k1_tex_2('#skF_5', '#skF_6')=C_192 | u1_struct_0(C_192)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_192, '#skF_5') | ~v1_pre_topc(C_192) | v2_struct_0(C_192) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1562])).
% 4.69/1.83  tff(c_1571, plain, (![C_193]: (k1_tex_2('#skF_5', '#skF_6')=C_193 | u1_struct_0(C_193)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_193, '#skF_5') | ~v1_pre_topc(C_193) | v2_struct_0(C_193))), inference(negUnitSimplification, [status(thm)], [c_66, c_1569])).
% 4.69/1.83  tff(c_1574, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6') | u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))!=k1_tarski('#skF_6') | ~v1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_1258, c_1571])).
% 4.69/1.83  tff(c_1577, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6') | v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_1225, c_1574])).
% 4.69/1.83  tff(c_1578, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_607, c_1577])).
% 4.69/1.83  tff(c_1582, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1258])).
% 4.69/1.83  tff(c_1583, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_607])).
% 4.69/1.83  tff(c_611, plain, (![A_107, B_108]: (v1_tdlat_3(k1_tex_2(A_107, B_108)) | ~v2_pre_topc(k1_tex_2(A_107, B_108)) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.69/1.83  tff(c_626, plain, (v1_tdlat_3(k1_tex_2('#skF_5', '#skF_6')) | ~v2_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_611])).
% 4.69/1.83  tff(c_632, plain, (v1_tdlat_3(k1_tex_2('#skF_5', '#skF_6')) | ~v2_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_626])).
% 4.69/1.83  tff(c_633, plain, (v1_tdlat_3(k1_tex_2('#skF_5', '#skF_6')) | ~v2_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_632])).
% 4.69/1.83  tff(c_634, plain, (~v2_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_633])).
% 4.69/1.83  tff(c_755, plain, (![A_117, B_118]: (u1_struct_0('#skF_4'(A_117, B_118))=B_118 | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | v1_xboole_0(B_118) | ~l1_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_770, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_755])).
% 4.69/1.83  tff(c_790, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6') | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_770])).
% 4.69/1.83  tff(c_791, plain, (u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_790])).
% 4.69/1.83  tff(c_716, plain, (![A_115, B_116]: (m1_pre_topc('#skF_4'(A_115, B_116), A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | v1_xboole_0(B_116) | ~l1_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.69/1.83  tff(c_727, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_716])).
% 4.69/1.83  tff(c_744, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_727])).
% 4.69/1.83  tff(c_745, plain, (m1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_82, c_744])).
% 4.69/1.83  tff(c_1080, plain, (![A_147, B_148, C_149]: (k1_tex_2(A_147, B_148)=C_149 | u1_struct_0(C_149)!=k6_domain_1(u1_struct_0(A_147), B_148) | ~m1_pre_topc(C_149, A_147) | ~v1_pre_topc(C_149) | v2_struct_0(C_149) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.69/1.83  tff(c_1092, plain, (![C_149]: (k1_tex_2('#skF_5', '#skF_6')=C_149 | u1_struct_0(C_149)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_149, '#skF_5') | ~v1_pre_topc(C_149) | v2_struct_0(C_149) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_1080])).
% 4.69/1.83  tff(c_1099, plain, (![C_149]: (k1_tex_2('#skF_5', '#skF_6')=C_149 | u1_struct_0(C_149)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_149, '#skF_5') | ~v1_pre_topc(C_149) | v2_struct_0(C_149) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1092])).
% 4.69/1.83  tff(c_1101, plain, (![C_150]: (k1_tex_2('#skF_5', '#skF_6')=C_150 | u1_struct_0(C_150)!=k1_tarski('#skF_6') | ~m1_pre_topc(C_150, '#skF_5') | ~v1_pre_topc(C_150) | v2_struct_0(C_150))), inference(negUnitSimplification, [status(thm)], [c_66, c_1099])).
% 4.69/1.83  tff(c_1104, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6') | u1_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))!=k1_tarski('#skF_6') | ~v1_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_745, c_1101])).
% 4.69/1.83  tff(c_1107, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6') | v2_struct_0('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_791, c_1104])).
% 4.69/1.83  tff(c_1108, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_6'))=k1_tex_2('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_607, c_1107])).
% 4.69/1.83  tff(c_64, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.69/1.83  tff(c_28, plain, (![B_15, A_13]: (v2_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.69/1.83  tff(c_751, plain, (v2_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_745, c_28])).
% 4.69/1.83  tff(c_754, plain, (v2_pre_topc('#skF_4'('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_751])).
% 4.69/1.83  tff(c_1111, plain, (v2_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_754])).
% 4.69/1.83  tff(c_1116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_634, c_1111])).
% 4.69/1.83  tff(c_1117, plain, (v1_tdlat_3(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_633])).
% 4.69/1.83  tff(c_1580, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1225])).
% 4.69/1.83  tff(c_54, plain, (![B_42, A_38]: (v2_tex_2(u1_struct_0(B_42), A_38) | ~v1_tdlat_3(B_42) | ~m1_subset_1(u1_struct_0(B_42), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_42, A_38) | v2_struct_0(B_42) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.69/1.83  tff(c_1621, plain, (![A_38]: (v2_tex_2(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')), A_38) | ~v1_tdlat_3(k1_tex_2('#skF_5', '#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), A_38) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(superposition, [status(thm), theory('equality')], [c_1580, c_54])).
% 4.69/1.83  tff(c_1664, plain, (![A_38]: (v2_tex_2(k1_tarski('#skF_6'), A_38) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), A_38) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc(A_38) | v2_struct_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_1580, c_1621])).
% 4.69/1.83  tff(c_1678, plain, (![A_194]: (v2_tex_2(k1_tarski('#skF_6'), A_194) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), A_194) | ~l1_pre_topc(A_194) | v2_struct_0(A_194))), inference(negUnitSimplification, [status(thm)], [c_1583, c_1664])).
% 4.69/1.83  tff(c_1684, plain, (v2_tex_2(k1_tarski('#skF_6'), '#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_228, c_1678])).
% 4.69/1.83  tff(c_1693, plain, (v2_tex_2(k1_tarski('#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1582, c_1684])).
% 4.69/1.83  tff(c_1695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_219, c_1693])).
% 4.69/1.83  tff(c_1697, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_121])).
% 4.69/1.83  tff(c_32, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.69/1.83  tff(c_1711, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1697, c_32])).
% 4.69/1.83  tff(c_1714, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_1711])).
% 4.69/1.83  tff(c_1717, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_1714])).
% 4.69/1.83  tff(c_1721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1717])).
% 4.69/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.83  
% 4.69/1.83  Inference rules
% 4.69/1.83  ----------------------
% 4.69/1.83  #Ref     : 0
% 4.69/1.83  #Sup     : 328
% 4.69/1.83  #Fact    : 0
% 4.69/1.83  #Define  : 0
% 4.69/1.83  #Split   : 4
% 4.69/1.83  #Chain   : 0
% 4.69/1.83  #Close   : 0
% 4.69/1.83  
% 4.69/1.83  Ordering : KBO
% 4.69/1.83  
% 4.69/1.83  Simplification rules
% 4.69/1.83  ----------------------
% 4.69/1.83  #Subsume      : 54
% 4.69/1.83  #Demod        : 183
% 4.69/1.83  #Tautology    : 102
% 4.69/1.83  #SimpNegUnit  : 154
% 4.69/1.83  #BackRed      : 13
% 4.69/1.83  
% 4.69/1.83  #Partial instantiations: 0
% 4.69/1.83  #Strategies tried      : 1
% 4.69/1.83  
% 4.69/1.83  Timing (in seconds)
% 4.69/1.83  ----------------------
% 4.69/1.83  Preprocessing        : 0.35
% 4.69/1.83  Parsing              : 0.18
% 4.69/1.83  CNF conversion       : 0.03
% 4.69/1.83  Main loop            : 0.66
% 4.69/1.83  Inferencing          : 0.23
% 4.69/1.83  Reduction            : 0.23
% 4.69/1.83  Demodulation         : 0.14
% 4.69/1.83  BG Simplification    : 0.03
% 4.69/1.83  Subsumption          : 0.12
% 4.69/1.83  Abstraction          : 0.04
% 4.69/1.83  MUC search           : 0.00
% 4.69/1.83  Cooper               : 0.00
% 4.69/1.83  Total                : 1.08
% 4.69/1.83  Index Insertion      : 0.00
% 4.69/1.83  Index Deletion       : 0.00
% 4.69/1.83  Index Matching       : 0.00
% 4.69/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
