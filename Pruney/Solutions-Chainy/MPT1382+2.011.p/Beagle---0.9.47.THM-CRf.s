%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 255 expanded)
%              Number of leaves         :   29 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 980 expanded)
%              Number of equality atoms :    7 (  27 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_28,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_300,plain,(
    ! [B_78,A_79,C_80] :
      ( r2_hidden(B_78,k1_tops_1(A_79,C_80))
      | ~ m1_connsp_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_78,u1_struct_0(A_79))
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_305,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_78)
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_309,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_78)
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_305])).

tff(c_310,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_78)
      | ~ m1_subset_1(B_78,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_309])).

tff(c_59,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_80,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k1_tops_1(A_55,B_56),B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_89,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_85])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    k2_xboole_0(k1_tops_1('#skF_2','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_89,c_8])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_97,plain,(
    ! [C_7] :
      ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),C_7)
      | ~ r1_tarski('#skF_4',C_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_6])).

tff(c_192,plain,(
    ! [A_71,B_72] :
      ( k1_tops_1(A_71,k1_tops_1(A_71,B_72)) = k1_tops_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_197,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_192])).

tff(c_201,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_55,A_10] :
      ( r1_tarski(k1_tops_1(A_55,A_10),A_10)
      | ~ l1_pre_topc(A_55)
      | ~ r1_tarski(A_10,u1_struct_0(A_55)) ) ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_208,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_86])).

tff(c_214,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_208])).

tff(c_223,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_226,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_97,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_226])).

tff(c_232,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_361,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_connsp_2(C_85,A_86,B_87)
      | ~ r2_hidden(B_87,k1_tops_1(A_86,C_85))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_365,plain,(
    ! [B_87] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_87)
      | ~ r2_hidden(B_87,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_361])).

tff(c_374,plain,(
    ! [B_87] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_87)
      | ~ r2_hidden(B_87,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_365])).

tff(c_375,plain,(
    ! [B_87] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_87)
      | ~ r2_hidden(B_87,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_87,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_374])).

tff(c_423,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_375])).

tff(c_426,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_423])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_426])).

tff(c_466,plain,(
    ! [B_92] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_92)
      | ~ r2_hidden(B_92,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_92,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_375])).

tff(c_142,plain,(
    ! [A_61,B_62] :
      ( v3_pre_topc(k1_tops_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_147,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_151,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_147])).

tff(c_46,plain,(
    ! [D_47] :
      ( ~ r1_tarski(D_47,'#skF_4')
      | ~ v3_pre_topc(D_47,'#skF_2')
      | ~ m1_connsp_2(D_47,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    ! [A_10] :
      ( ~ r1_tarski(A_10,'#skF_4')
      | ~ v3_pre_topc(A_10,'#skF_2')
      | ~ m1_connsp_2(A_10,'#skF_2','#skF_3')
      | v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_46])).

tff(c_239,plain,
    ( ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_232,c_54])).

tff(c_250,plain,
    ( ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_89,c_239])).

tff(c_299,plain,(
    ~ m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_469,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_466,c_299])).

tff(c_474,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_469])).

tff(c_481,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_310,c_474])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_481])).

tff(c_486,plain,(
    v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_488,plain,(
    ! [B_93,A_94,C_95] :
      ( r2_hidden(B_93,k1_tops_1(A_94,C_95))
      | ~ m1_connsp_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_subset_1(B_93,u1_struct_0(A_94))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_493,plain,(
    ! [B_93] :
      ( r2_hidden(B_93,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_488])).

tff(c_497,plain,(
    ! [B_93] :
      ( r2_hidden(B_93,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_93)
      | ~ m1_subset_1(B_93,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_493])).

tff(c_552,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_497])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_555,plain,(
    ! [B_96] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_96)
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_552,c_2])).

tff(c_559,plain,(
    ! [B_97] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_97)
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_555])).

tff(c_562,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_559])).

tff(c_566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_562])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.87/1.46  
% 2.87/1.46  %Foreground sorts:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Background operators:
% 2.87/1.46  
% 2.87/1.46  
% 2.87/1.46  %Foreground operators:
% 2.87/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.87/1.46  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.87/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.46  
% 3.02/1.48  tff(f_125, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.02/1.48  tff(f_81, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.02/1.48  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.48  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.02/1.48  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.02/1.48  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.02/1.48  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 3.02/1.48  tff(f_51, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.02/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.02/1.48  tff(c_28, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_32, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_300, plain, (![B_78, A_79, C_80]: (r2_hidden(B_78, k1_tops_1(A_79, C_80)) | ~m1_connsp_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_78, u1_struct_0(A_79)) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.48  tff(c_305, plain, (![B_78]: (r2_hidden(B_78, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_78) | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_300])).
% 3.02/1.48  tff(c_309, plain, (![B_78]: (r2_hidden(B_78, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_78) | ~m1_subset_1(B_78, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_305])).
% 3.02/1.48  tff(c_310, plain, (![B_78]: (r2_hidden(B_78, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_78) | ~m1_subset_1(B_78, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_309])).
% 3.02/1.48  tff(c_59, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.48  tff(c_67, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_59])).
% 3.02/1.48  tff(c_80, plain, (![A_55, B_56]: (r1_tarski(k1_tops_1(A_55, B_56), B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.48  tff(c_85, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_80])).
% 3.02/1.48  tff(c_89, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_85])).
% 3.02/1.48  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.02/1.48  tff(c_93, plain, (k2_xboole_0(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_89, c_8])).
% 3.02/1.48  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.02/1.48  tff(c_97, plain, (![C_7]: (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), C_7) | ~r1_tarski('#skF_4', C_7))), inference(superposition, [status(thm), theory('equality')], [c_93, c_6])).
% 3.02/1.48  tff(c_192, plain, (![A_71, B_72]: (k1_tops_1(A_71, k1_tops_1(A_71, B_72))=k1_tops_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.02/1.48  tff(c_197, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_192])).
% 3.02/1.48  tff(c_201, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_197])).
% 3.02/1.48  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.02/1.48  tff(c_86, plain, (![A_55, A_10]: (r1_tarski(k1_tops_1(A_55, A_10), A_10) | ~l1_pre_topc(A_55) | ~r1_tarski(A_10, u1_struct_0(A_55)))), inference(resolution, [status(thm)], [c_12, c_80])).
% 3.02/1.48  tff(c_208, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_86])).
% 3.02/1.48  tff(c_214, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_208])).
% 3.02/1.48  tff(c_223, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_214])).
% 3.02/1.48  tff(c_226, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_97, c_223])).
% 3.02/1.48  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_226])).
% 3.02/1.48  tff(c_232, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_214])).
% 3.02/1.48  tff(c_361, plain, (![C_85, A_86, B_87]: (m1_connsp_2(C_85, A_86, B_87) | ~r2_hidden(B_87, k1_tops_1(A_86, C_85)) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.48  tff(c_365, plain, (![B_87]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_87) | ~r2_hidden(B_87, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_361])).
% 3.02/1.48  tff(c_374, plain, (![B_87]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_87) | ~r2_hidden(B_87, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_87, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_365])).
% 3.02/1.48  tff(c_375, plain, (![B_87]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_87) | ~r2_hidden(B_87, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_87, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_374])).
% 3.02/1.48  tff(c_423, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_375])).
% 3.02/1.48  tff(c_426, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_423])).
% 3.02/1.48  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_426])).
% 3.02/1.48  tff(c_466, plain, (![B_92]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_92) | ~r2_hidden(B_92, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_92, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_375])).
% 3.02/1.48  tff(c_142, plain, (![A_61, B_62]: (v3_pre_topc(k1_tops_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.48  tff(c_147, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_142])).
% 3.02/1.48  tff(c_151, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_147])).
% 3.02/1.48  tff(c_46, plain, (![D_47]: (~r1_tarski(D_47, '#skF_4') | ~v3_pre_topc(D_47, '#skF_2') | ~m1_connsp_2(D_47, '#skF_2', '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_47))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.02/1.48  tff(c_54, plain, (![A_10]: (~r1_tarski(A_10, '#skF_4') | ~v3_pre_topc(A_10, '#skF_2') | ~m1_connsp_2(A_10, '#skF_2', '#skF_3') | v1_xboole_0(A_10) | ~r1_tarski(A_10, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_12, c_46])).
% 3.02/1.48  tff(c_239, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_232, c_54])).
% 3.02/1.48  tff(c_250, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_89, c_239])).
% 3.02/1.48  tff(c_299, plain, (~m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_250])).
% 3.02/1.48  tff(c_469, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_466, c_299])).
% 3.02/1.48  tff(c_474, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_469])).
% 3.02/1.48  tff(c_481, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_310, c_474])).
% 3.02/1.48  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_481])).
% 3.02/1.48  tff(c_486, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_250])).
% 3.02/1.48  tff(c_488, plain, (![B_93, A_94, C_95]: (r2_hidden(B_93, k1_tops_1(A_94, C_95)) | ~m1_connsp_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_subset_1(B_93, u1_struct_0(A_94)) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.48  tff(c_493, plain, (![B_93]: (r2_hidden(B_93, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_488])).
% 3.02/1.48  tff(c_497, plain, (![B_93]: (r2_hidden(B_93, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_93) | ~m1_subset_1(B_93, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_493])).
% 3.02/1.48  tff(c_552, plain, (![B_96]: (r2_hidden(B_96, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_38, c_497])).
% 3.02/1.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.02/1.48  tff(c_555, plain, (![B_96]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_96) | ~m1_subset_1(B_96, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_552, c_2])).
% 3.02/1.48  tff(c_559, plain, (![B_97]: (~m1_connsp_2('#skF_4', '#skF_2', B_97) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_486, c_555])).
% 3.02/1.48  tff(c_562, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_559])).
% 3.02/1.48  tff(c_566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_562])).
% 3.02/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  Inference rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Ref     : 0
% 3.02/1.48  #Sup     : 111
% 3.02/1.48  #Fact    : 0
% 3.02/1.48  #Define  : 0
% 3.02/1.48  #Split   : 6
% 3.02/1.48  #Chain   : 0
% 3.02/1.48  #Close   : 0
% 3.02/1.48  
% 3.02/1.48  Ordering : KBO
% 3.02/1.48  
% 3.02/1.48  Simplification rules
% 3.02/1.48  ----------------------
% 3.02/1.48  #Subsume      : 8
% 3.02/1.48  #Demod        : 99
% 3.02/1.48  #Tautology    : 53
% 3.02/1.48  #SimpNegUnit  : 12
% 3.02/1.48  #BackRed      : 0
% 3.02/1.48  
% 3.02/1.48  #Partial instantiations: 0
% 3.02/1.48  #Strategies tried      : 1
% 3.02/1.48  
% 3.02/1.48  Timing (in seconds)
% 3.02/1.48  ----------------------
% 3.02/1.48  Preprocessing        : 0.32
% 3.02/1.48  Parsing              : 0.19
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.32
% 3.02/1.48  Inferencing          : 0.12
% 3.02/1.48  Reduction            : 0.09
% 3.02/1.48  Demodulation         : 0.06
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.06
% 3.02/1.48  Abstraction          : 0.01
% 3.02/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.68
% 3.02/1.48  Index Insertion      : 0.00
% 3.02/1.48  Index Deletion       : 0.00
% 3.02/1.48  Index Matching       : 0.00
% 3.02/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
