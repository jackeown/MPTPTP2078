%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:24 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 778 expanded)
%              Number of leaves         :   36 ( 292 expanded)
%              Depth                    :   24
%              Number of atoms          :  191 (2748 expanded)
%              Number of equality atoms :   11 ( 210 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_133,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_55,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_55])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_402,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_3'(A_124,B_125),B_125)
      | v2_tex_2(B_125,A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_417,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_402])).

tff(c_425,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_417])).

tff(c_426,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40,c_425])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_462,plain,(
    ! [B_127] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_127)
      | ~ r1_tarski('#skF_5',B_127) ) ),
    inference(resolution,[status(thm)],[c_426,c_2])).

tff(c_563,plain,(
    ! [B_134,B_135] :
      ( r2_hidden('#skF_3'('#skF_4','#skF_5'),B_134)
      | ~ r1_tarski(B_135,B_134)
      | ~ r1_tarski('#skF_5',B_135) ) ),
    inference(resolution,[status(thm)],[c_462,c_2])).

tff(c_583,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_59,c_563])).

tff(c_595,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_583])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_249,plain,(
    ! [A_95,B_96] :
      ( v4_pre_topc(k2_pre_topc(A_95,B_96),A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_262,plain,(
    ! [A_95,A_10] :
      ( v4_pre_topc(k2_pre_topc(A_95,A_10),A_95)
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | ~ r1_tarski(A_10,u1_struct_0(A_95)) ) ),
    inference(resolution,[status(thm)],[c_16,c_249])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k2_pre_topc(A_15,B_16),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_90,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_61,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_109,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_609,plain,(
    m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_595,c_12])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( k6_domain_1(A_17,B_18) = k1_tarski(B_18)
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_628,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_609,c_22])).

tff(c_631,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_628])).

tff(c_42,plain,(
    ! [C_43] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),C_43))) = k6_domain_1(u1_struct_0('#skF_4'),C_43)
      | ~ r2_hidden(C_43,'#skF_5')
      | ~ m1_subset_1(C_43,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_703,plain,
    ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5')))) = k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_42])).

tff(c_707,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5')))) = k1_tarski('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_426,c_631,c_703])).

tff(c_34,plain,(
    ! [A_25,B_33,D_38] :
      ( k9_subset_1(u1_struct_0(A_25),B_33,D_38) != k6_domain_1(u1_struct_0(A_25),'#skF_3'(A_25,B_33))
      | ~ v3_pre_topc(D_38,A_25)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0(A_25)))
      | v2_tex_2(B_33,A_25)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_927,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_3'('#skF_4','#skF_5')) != k1_tarski('#skF_3'('#skF_4','#skF_5'))
    | ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_34])).

tff(c_931,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_631,c_927])).

tff(c_932,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40,c_931])).

tff(c_1091,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_932])).

tff(c_1094,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_1091])).

tff(c_1100,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1094])).

tff(c_1105,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_1100])).

tff(c_1114,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_1105])).

tff(c_1120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_1114])).

tff(c_1121,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_48,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1122,plain,(
    m1_subset_1(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_932])).

tff(c_26,plain,(
    ! [B_24,A_21] :
      ( v3_pre_topc(B_24,A_21)
      | ~ v4_pre_topc(B_24,A_21)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ v3_tdlat_3(A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1130,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1122,c_26])).

tff(c_1150,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4')
    | ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_1130])).

tff(c_1151,plain,(
    ~ v4_pre_topc(k2_pre_topc('#skF_4',k1_tarski('#skF_3'('#skF_4','#skF_5'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1121,c_1150])).

tff(c_1223,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_262,c_1151])).

tff(c_1226,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'('#skF_4','#skF_5')),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1223])).

tff(c_1235,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_10,c_1226])).

tff(c_1241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_1235])).

tff(c_1242,plain,(
    ! [A_61] : ~ r2_hidden(A_61,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1848,plain,(
    ! [A_283,B_284] :
      ( r2_hidden('#skF_3'(A_283,B_284),B_284)
      | v2_tex_2(B_284,A_283)
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1863,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1848])).

tff(c_1871,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_1863])).

tff(c_1873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_40,c_1242,c_1871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:24:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  
% 3.93/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.66  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 3.93/1.66  
% 3.93/1.66  %Foreground sorts:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Background operators:
% 3.93/1.66  
% 3.93/1.66  
% 3.93/1.66  %Foreground operators:
% 3.93/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.93/1.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.93/1.66  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.93/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.93/1.66  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.93/1.66  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.93/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.66  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.93/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.66  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.93/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.93/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.93/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.93/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.93/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.93/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.93/1.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.93/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.66  
% 3.93/1.68  tff(f_133, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 3.93/1.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.93/1.68  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.93/1.68  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 3.93/1.68  tff(f_36, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.93/1.68  tff(f_72, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.93/1.68  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.93/1.68  tff(f_51, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.93/1.68  tff(f_40, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.93/1.68  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.93/1.68  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 3.93/1.68  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_40, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.68  tff(c_84, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.68  tff(c_89, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_84])).
% 3.93/1.68  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_55, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.93/1.68  tff(c_59, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_55])).
% 3.93/1.68  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_402, plain, (![A_124, B_125]: (r2_hidden('#skF_3'(A_124, B_125), B_125) | v2_tex_2(B_125, A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.93/1.68  tff(c_417, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_402])).
% 3.93/1.68  tff(c_425, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_417])).
% 3.93/1.68  tff(c_426, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_40, c_425])).
% 3.93/1.68  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.93/1.68  tff(c_462, plain, (![B_127]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_127) | ~r1_tarski('#skF_5', B_127))), inference(resolution, [status(thm)], [c_426, c_2])).
% 3.93/1.68  tff(c_563, plain, (![B_134, B_135]: (r2_hidden('#skF_3'('#skF_4', '#skF_5'), B_134) | ~r1_tarski(B_135, B_134) | ~r1_tarski('#skF_5', B_135))), inference(resolution, [status(thm)], [c_462, c_2])).
% 3.93/1.68  tff(c_583, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_59, c_563])).
% 3.93/1.68  tff(c_595, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_583])).
% 3.93/1.68  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.93/1.68  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.93/1.68  tff(c_249, plain, (![A_95, B_96]: (v4_pre_topc(k2_pre_topc(A_95, B_96), A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.93/1.68  tff(c_262, plain, (![A_95, A_10]: (v4_pre_topc(k2_pre_topc(A_95, A_10), A_95) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | ~r1_tarski(A_10, u1_struct_0(A_95)))), inference(resolution, [status(thm)], [c_16, c_249])).
% 3.93/1.68  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k2_pre_topc(A_15, B_16), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.93/1.68  tff(c_90, plain, (![C_59, B_60, A_61]: (~v1_xboole_0(C_59) | ~m1_subset_1(B_60, k1_zfmisc_1(C_59)) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.93/1.68  tff(c_96, plain, (![A_61]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_61, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_90])).
% 3.93/1.68  tff(c_109, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_96])).
% 3.93/1.68  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.93/1.68  tff(c_609, plain, (m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_595, c_12])).
% 3.93/1.68  tff(c_22, plain, (![A_17, B_18]: (k6_domain_1(A_17, B_18)=k1_tarski(B_18) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.93/1.68  tff(c_628, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_609, c_22])).
% 3.93/1.68  tff(c_631, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_109, c_628])).
% 3.93/1.68  tff(c_42, plain, (![C_43]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), C_43)))=k6_domain_1(u1_struct_0('#skF_4'), C_43) | ~r2_hidden(C_43, '#skF_5') | ~m1_subset_1(C_43, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_703, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))))=k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5')) | ~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_631, c_42])).
% 3.93/1.68  tff(c_707, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))))=k1_tarski('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_426, c_631, c_703])).
% 3.93/1.68  tff(c_34, plain, (![A_25, B_33, D_38]: (k9_subset_1(u1_struct_0(A_25), B_33, D_38)!=k6_domain_1(u1_struct_0(A_25), '#skF_3'(A_25, B_33)) | ~v3_pre_topc(D_38, A_25) | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0(A_25))) | v2_tex_2(B_33, A_25) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.93/1.68  tff(c_927, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_3'('#skF_4', '#skF_5'))!=k1_tarski('#skF_3'('#skF_4', '#skF_5')) | ~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_707, c_34])).
% 3.93/1.68  tff(c_931, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_631, c_927])).
% 3.93/1.68  tff(c_932, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_40, c_931])).
% 3.93/1.68  tff(c_1091, plain, (~m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_932])).
% 3.93/1.68  tff(c_1094, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_1091])).
% 3.93/1.68  tff(c_1100, plain, (~m1_subset_1(k1_tarski('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1094])).
% 3.93/1.68  tff(c_1105, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_1100])).
% 3.93/1.68  tff(c_1114, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_1105])).
% 3.93/1.68  tff(c_1120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_1114])).
% 3.93/1.68  tff(c_1121, plain, (~v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(splitRight, [status(thm)], [c_932])).
% 3.93/1.68  tff(c_48, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.68  tff(c_1122, plain, (m1_subset_1(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_932])).
% 3.93/1.68  tff(c_26, plain, (![B_24, A_21]: (v3_pre_topc(B_24, A_21) | ~v4_pre_topc(B_24, A_21) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_21))) | ~v3_tdlat_3(A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.93/1.68  tff(c_1130, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v3_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1122, c_26])).
% 3.93/1.68  tff(c_1150, plain, (v3_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4') | ~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_1130])).
% 3.93/1.68  tff(c_1151, plain, (~v4_pre_topc(k2_pre_topc('#skF_4', k1_tarski('#skF_3'('#skF_4', '#skF_5'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1121, c_1150])).
% 3.93/1.68  tff(c_1223, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_262, c_1151])).
% 3.93/1.68  tff(c_1226, plain, (~r1_tarski(k1_tarski('#skF_3'('#skF_4', '#skF_5')), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1223])).
% 3.93/1.68  tff(c_1235, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_10, c_1226])).
% 3.93/1.68  tff(c_1241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_595, c_1235])).
% 3.93/1.68  tff(c_1242, plain, (![A_61]: (~r2_hidden(A_61, '#skF_5'))), inference(splitRight, [status(thm)], [c_96])).
% 3.93/1.68  tff(c_1848, plain, (![A_283, B_284]: (r2_hidden('#skF_3'(A_283, B_284), B_284) | v2_tex_2(B_284, A_283) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.93/1.68  tff(c_1863, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1848])).
% 3.93/1.68  tff(c_1871, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_1863])).
% 3.93/1.68  tff(c_1873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_40, c_1242, c_1871])).
% 3.93/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.68  
% 3.93/1.68  Inference rules
% 3.93/1.68  ----------------------
% 3.93/1.68  #Ref     : 0
% 3.93/1.68  #Sup     : 424
% 3.93/1.68  #Fact    : 0
% 3.93/1.68  #Define  : 0
% 3.93/1.68  #Split   : 10
% 3.93/1.68  #Chain   : 0
% 3.93/1.68  #Close   : 0
% 3.93/1.68  
% 3.93/1.68  Ordering : KBO
% 3.93/1.68  
% 3.93/1.68  Simplification rules
% 3.93/1.68  ----------------------
% 3.93/1.68  #Subsume      : 144
% 3.93/1.68  #Demod        : 82
% 3.93/1.68  #Tautology    : 49
% 3.93/1.68  #SimpNegUnit  : 24
% 3.93/1.68  #BackRed      : 10
% 4.23/1.68  
% 4.23/1.68  #Partial instantiations: 0
% 4.23/1.68  #Strategies tried      : 1
% 4.23/1.68  
% 4.23/1.68  Timing (in seconds)
% 4.23/1.68  ----------------------
% 4.23/1.68  Preprocessing        : 0.34
% 4.23/1.68  Parsing              : 0.18
% 4.23/1.68  CNF conversion       : 0.02
% 4.23/1.68  Main loop            : 0.58
% 4.23/1.68  Inferencing          : 0.21
% 4.23/1.68  Reduction            : 0.16
% 4.23/1.68  Demodulation         : 0.10
% 4.23/1.68  BG Simplification    : 0.03
% 4.23/1.68  Subsumption          : 0.13
% 4.23/1.68  Abstraction          : 0.03
% 4.23/1.68  MUC search           : 0.00
% 4.23/1.68  Cooper               : 0.00
% 4.23/1.68  Total                : 0.95
% 4.23/1.68  Index Insertion      : 0.00
% 4.23/1.68  Index Deletion       : 0.00
% 4.23/1.68  Index Matching       : 0.00
% 4.23/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
