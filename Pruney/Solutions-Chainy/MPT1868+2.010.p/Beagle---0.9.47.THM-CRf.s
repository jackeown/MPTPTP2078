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
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 230 expanded)
%              Number of leaves         :   34 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 ( 638 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_57,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_65,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_66,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_12,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_12])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_69])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_75])).

tff(c_81,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_48,B_49] :
      ( m1_pre_topc(k1_tex_2(A_48,B_49),A_48)
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_105,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_103])).

tff(c_108,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_105])).

tff(c_109,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_108])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_46,B_47] :
      ( ~ v2_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_98,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_95])).

tff(c_101,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_102,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_101])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v2_pre_topc(B_8)
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,
    ( v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_109,c_8])).

tff(c_115,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_112])).

tff(c_116,plain,(
    ! [A_50,B_51] :
      ( v1_tdlat_3(k1_tex_2(A_50,B_51))
      | ~ v2_pre_topc(k1_tex_2(A_50,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_119,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_122,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_115,c_119])).

tff(c_123,plain,(
    v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_122])).

tff(c_82,plain,(
    ! [A_44,B_45] :
      ( v1_pre_topc(k1_tex_2(A_44,B_45))
      | ~ m1_subset_1(B_45,u1_struct_0(A_44))
      | ~ l1_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_85,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_88,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_89,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_88])).

tff(c_80,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_158,plain,(
    ! [A_64,B_65] :
      ( k6_domain_1(u1_struct_0(A_64),B_65) = u1_struct_0(k1_tex_2(A_64,B_65))
      | ~ m1_pre_topc(k1_tex_2(A_64,B_65),A_64)
      | ~ v1_pre_topc(k1_tex_2(A_64,B_65))
      | v2_struct_0(k1_tex_2(A_64,B_65))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_160,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_109,c_158])).

tff(c_163,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = k1_tarski('#skF_2')
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_89,c_80,c_160])).

tff(c_164,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_102,c_163])).

tff(c_30,plain,(
    ! [B_29,A_25] :
      ( v2_tex_2(u1_struct_0(B_29),A_25)
      | ~ v1_tdlat_3(B_29)
      | ~ m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_29,A_25)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_176,plain,(
    ! [A_25] :
      ( v2_tex_2(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),A_25)
      | ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_25)
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_30])).

tff(c_205,plain,(
    ! [A_25] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_25)
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_25)
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_164,c_176])).

tff(c_220,plain,(
    ! [A_66] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_66)
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_66)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_205])).

tff(c_229,plain,(
    ! [A_67] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_67)
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_67)
      | ~ l1_pre_topc(A_67)
      | v2_struct_0(A_67)
      | ~ r2_hidden('#skF_2',u1_struct_0(A_67)) ) ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_34,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_90,plain,(
    ~ v2_tex_2(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_34])).

tff(c_232,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_229,c_90])).

tff(c_235,plain,
    ( v2_struct_0('#skF_1')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109,c_232])).

tff(c_236,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_235])).

tff(c_239,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_236])).

tff(c_242,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.34  
% 2.17/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.47/1.34  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.47/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.47/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.34  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.47/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.47/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.47/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.47/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.35  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.47/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.35  
% 2.47/1.36  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.47/1.36  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.47/1.36  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.47/1.36  tff(f_58, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.47/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.47/1.36  tff(f_99, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.47/1.36  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.47/1.36  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.47/1.36  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 2.47/1.36  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.47/1.36  tff(f_133, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.47/1.36  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.47/1.36  tff(c_10, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.47/1.36  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.47/1.36  tff(c_36, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.47/1.36  tff(c_57, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.36  tff(c_65, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.47/1.36  tff(c_66, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_65])).
% 2.47/1.36  tff(c_12, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.36  tff(c_69, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_12])).
% 2.47/1.36  tff(c_72, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_69])).
% 2.47/1.36  tff(c_75, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_72])).
% 2.47/1.36  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_75])).
% 2.47/1.36  tff(c_81, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_65])).
% 2.47/1.36  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.36  tff(c_103, plain, (![A_48, B_49]: (m1_pre_topc(k1_tex_2(A_48, B_49), A_48) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.47/1.36  tff(c_105, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_103])).
% 2.47/1.36  tff(c_108, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_105])).
% 2.47/1.36  tff(c_109, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_108])).
% 2.47/1.36  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.36  tff(c_95, plain, (![A_46, B_47]: (~v2_struct_0(k1_tex_2(A_46, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.47/1.36  tff(c_98, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_95])).
% 2.47/1.36  tff(c_101, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_98])).
% 2.47/1.36  tff(c_102, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_101])).
% 2.47/1.36  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.47/1.36  tff(c_8, plain, (![B_8, A_6]: (v2_pre_topc(B_8) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.36  tff(c_112, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_109, c_8])).
% 2.47/1.36  tff(c_115, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_112])).
% 2.47/1.36  tff(c_116, plain, (![A_50, B_51]: (v1_tdlat_3(k1_tex_2(A_50, B_51)) | ~v2_pre_topc(k1_tex_2(A_50, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.47/1.36  tff(c_119, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_116])).
% 2.47/1.36  tff(c_122, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_115, c_119])).
% 2.47/1.36  tff(c_123, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_122])).
% 2.47/1.36  tff(c_82, plain, (![A_44, B_45]: (v1_pre_topc(k1_tex_2(A_44, B_45)) | ~m1_subset_1(B_45, u1_struct_0(A_44)) | ~l1_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.47/1.36  tff(c_85, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.47/1.36  tff(c_88, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_85])).
% 2.47/1.36  tff(c_89, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_88])).
% 2.47/1.36  tff(c_80, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_65])).
% 2.47/1.36  tff(c_158, plain, (![A_64, B_65]: (k6_domain_1(u1_struct_0(A_64), B_65)=u1_struct_0(k1_tex_2(A_64, B_65)) | ~m1_pre_topc(k1_tex_2(A_64, B_65), A_64) | ~v1_pre_topc(k1_tex_2(A_64, B_65)) | v2_struct_0(k1_tex_2(A_64, B_65)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.47/1.36  tff(c_160, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_109, c_158])).
% 2.47/1.36  tff(c_163, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=k1_tarski('#skF_2') | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_89, c_80, c_160])).
% 2.47/1.36  tff(c_164, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_102, c_163])).
% 2.47/1.36  tff(c_30, plain, (![B_29, A_25]: (v2_tex_2(u1_struct_0(B_29), A_25) | ~v1_tdlat_3(B_29) | ~m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_29, A_25) | v2_struct_0(B_29) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.47/1.36  tff(c_176, plain, (![A_25]: (v2_tex_2(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), A_25) | ~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_25) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(superposition, [status(thm), theory('equality')], [c_164, c_30])).
% 2.47/1.36  tff(c_205, plain, (![A_25]: (v2_tex_2(k1_tarski('#skF_2'), A_25) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_25) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_164, c_176])).
% 2.47/1.36  tff(c_220, plain, (![A_66]: (v2_tex_2(k1_tarski('#skF_2'), A_66) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_66))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_66) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_102, c_205])).
% 2.47/1.36  tff(c_229, plain, (![A_67]: (v2_tex_2(k1_tarski('#skF_2'), A_67) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_67) | ~l1_pre_topc(A_67) | v2_struct_0(A_67) | ~r2_hidden('#skF_2', u1_struct_0(A_67)))), inference(resolution, [status(thm)], [c_4, c_220])).
% 2.47/1.36  tff(c_34, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.47/1.36  tff(c_90, plain, (~v2_tex_2(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_34])).
% 2.47/1.36  tff(c_232, plain, (~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_229, c_90])).
% 2.47/1.36  tff(c_235, plain, (v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109, c_232])).
% 2.47/1.36  tff(c_236, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_235])).
% 2.47/1.36  tff(c_239, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_236])).
% 2.47/1.36  tff(c_242, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_239])).
% 2.47/1.36  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_242])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 37
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 2
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 4
% 2.47/1.36  #Demod        : 26
% 2.47/1.36  #Tautology    : 10
% 2.47/1.36  #SimpNegUnit  : 23
% 2.47/1.36  #BackRed      : 1
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.37  Preprocessing        : 0.35
% 2.47/1.37  Parsing              : 0.19
% 2.47/1.37  CNF conversion       : 0.02
% 2.47/1.37  Main loop            : 0.20
% 2.47/1.37  Inferencing          : 0.07
% 2.47/1.37  Reduction            : 0.06
% 2.47/1.37  Demodulation         : 0.04
% 2.47/1.37  BG Simplification    : 0.02
% 2.47/1.37  Subsumption          : 0.04
% 2.47/1.37  Abstraction          : 0.01
% 2.47/1.37  MUC search           : 0.00
% 2.47/1.37  Cooper               : 0.00
% 2.47/1.37  Total                : 0.59
% 2.47/1.37  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
