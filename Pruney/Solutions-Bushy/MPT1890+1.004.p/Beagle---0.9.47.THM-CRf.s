%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1890+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:39 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 372 expanded)
%              Number of leaves         :   32 ( 150 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 (1515 expanded)
%              Number of equality atoms :   31 ( 171 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_30,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_32,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_20,plain,(
    ! [A_17,B_25] :
      ( m1_subset_1('#skF_1'(A_17,B_25),u1_struct_0(A_17))
      | v2_tex_2(B_25,A_17)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17)
      | ~ v3_tdlat_3(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_70,plain,(
    ! [C_41,B_42,A_43] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_73,plain,(
    ! [A_43] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_43,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_74,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_277,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1('#skF_1'(A_75,B_76),u1_struct_0(A_75))
      | v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v3_tdlat_3(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k6_domain_1(A_12,B_13) = k1_tarski(B_13)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_917,plain,(
    ! [A_107,B_108] :
      ( k6_domain_1(u1_struct_0(A_107),'#skF_1'(A_107,B_108)) = k1_tarski('#skF_1'(A_107,B_108))
      | v1_xboole_0(u1_struct_0(A_107))
      | v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v3_tdlat_3(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_277,c_12])).

tff(c_928,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) = k1_tarski('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_917])).

tff(c_941,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) = k1_tarski('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_928])).

tff(c_942,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) = k1_tarski('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_74,c_941])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k6_domain_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_973,plain,
    ( m1_subset_1(k1_tarski('#skF_1'('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_8])).

tff(c_994,plain,
    ( m1_subset_1(k1_tarski('#skF_1'('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_973])).

tff(c_1027,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_1030,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1027])).

tff(c_1033,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_1030])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_1033])).

tff(c_1036,plain,(
    m1_subset_1(k1_tarski('#skF_1'('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v4_pre_topc(k2_pre_topc(A_10,B_11),A_10)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1074,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3'))),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1036,c_10])).

tff(c_1108,plain,(
    v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3'))),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1074])).

tff(c_1037,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_179,plain,(
    ! [A_67,B_68] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_68)
      | v2_tex_2(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v3_tdlat_3(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_186,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_179])).

tff(c_191,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_186])).

tff(c_192,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_191])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_89,plain,(
    ! [A_47,B_48,C_49] :
      ( k9_subset_1(A_47,B_48,C_49) = k3_xboole_0(B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_92,plain,(
    ! [B_48] : k9_subset_1(u1_struct_0('#skF_2'),B_48,'#skF_3') = k3_xboole_0(B_48,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_89])).

tff(c_113,plain,(
    ! [A_53,C_54,B_55] :
      ( k9_subset_1(A_53,C_54,B_55) = k9_subset_1(A_53,B_55,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_117,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_2'),B_55,'#skF_3') = k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_55) ),
    inference(resolution,[status(thm)],[c_28,c_113])).

tff(c_120,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',B_55) = k3_xboole_0(B_55,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_117])).

tff(c_26,plain,(
    ! [C_38] :
      ( k9_subset_1(u1_struct_0('#skF_2'),'#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_38))) = k6_domain_1(u1_struct_0('#skF_2'),C_38)
      | ~ r2_hidden(C_38,'#skF_3')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_121,plain,(
    ! [C_38] :
      ( k3_xboole_0(k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_38)),'#skF_3') = k6_domain_1(u1_struct_0('#skF_2'),C_38)
      | ~ r2_hidden(C_38,'#skF_3')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_26])).

tff(c_122,plain,(
    ! [C_38] :
      ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),C_38))) = k6_domain_1(u1_struct_0('#skF_2'),C_38)
      | ~ r2_hidden(C_38,'#skF_3')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_970,plain,
    ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3')))) = k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3'))
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_122])).

tff(c_993,plain,
    ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3')))) = k1_tarski('#skF_1'('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_942,c_970])).

tff(c_1366,plain,(
    k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3')))) = k1_tarski('#skF_1'('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1037,c_993])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k2_pre_topc(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_367,plain,(
    ! [A_88,B_89,D_90] :
      ( k9_subset_1(u1_struct_0(A_88),B_89,D_90) != k6_domain_1(u1_struct_0(A_88),'#skF_1'(A_88,B_89))
      | ~ v4_pre_topc(D_90,A_88)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(A_88)))
      | v2_tex_2(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88)
      | ~ v3_tdlat_3(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_380,plain,(
    ! [B_55] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) != k3_xboole_0(B_55,'#skF_3')
      | ~ v4_pre_topc(B_55,'#skF_2')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_367])).

tff(c_385,plain,(
    ! [B_55] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) != k3_xboole_0(B_55,'#skF_3')
      | ~ v4_pre_topc(B_55,'#skF_2')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_380])).

tff(c_431,plain,(
    ! [B_92] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) != k3_xboole_0(B_92,'#skF_3')
      | ~ v4_pre_topc(B_92,'#skF_2')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_385])).

tff(c_435,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) != k3_xboole_0(k2_pre_topc('#skF_2',B_7),'#skF_3')
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_431])).

tff(c_445,plain,(
    ! [B_7] :
      ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_1'('#skF_2','#skF_3')) != k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',B_7))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2,c_435])).

tff(c_1445,plain,(
    ! [B_118] :
      ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',B_118)) != k1_tarski('#skF_1'('#skF_2','#skF_3'))
      | ~ v4_pre_topc(k2_pre_topc('#skF_2',B_118),'#skF_2')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_445])).

tff(c_1448,plain,
    ( k3_xboole_0('#skF_3',k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3')))) != k1_tarski('#skF_1'('#skF_2','#skF_3'))
    | ~ v4_pre_topc(k2_pre_topc('#skF_2',k1_tarski('#skF_1'('#skF_2','#skF_3'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1036,c_1445])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1366,c_1448])).

tff(c_1470,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1575,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_1'(A_142,B_143),B_143)
      | v2_tex_2(B_143,A_142)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v3_tdlat_3(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1582,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1575])).

tff(c_1587,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1582])).

tff(c_1589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_1470,c_1587])).

%------------------------------------------------------------------------------
