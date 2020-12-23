%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:12 EST 2020

% Result     : Theorem 25.12s
% Output     : CNFRefutation 25.12s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 239 expanded)
%              Number of leaves         :   26 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 470 expanded)
%              Number of equality atoms :   30 (  81 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34905,plain,(
    ! [A_720,B_721,C_722] :
      ( k9_subset_1(A_720,B_721,C_722) = k3_xboole_0(B_721,C_722)
      | ~ m1_subset_1(C_722,k1_zfmisc_1(A_720)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34918,plain,(
    ! [B_721] : k9_subset_1(u1_struct_0('#skF_1'),B_721,'#skF_3') = k3_xboole_0(B_721,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_34905])).

tff(c_34987,plain,(
    ! [A_730,C_731,B_732] :
      ( k9_subset_1(A_730,C_731,B_732) = k9_subset_1(A_730,B_732,C_731)
      | ~ m1_subset_1(C_731,k1_zfmisc_1(A_730)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34995,plain,(
    ! [B_732] : k9_subset_1(u1_struct_0('#skF_1'),B_732,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_732) ),
    inference(resolution,[status(thm)],[c_26,c_34987])).

tff(c_35174,plain,(
    ! [B_743] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_743) = k3_xboole_0(B_743,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34918,c_34995])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34919,plain,(
    ! [B_721] : k9_subset_1(u1_struct_0('#skF_1'),B_721,'#skF_2') = k3_xboole_0(B_721,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_34905])).

tff(c_35181,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35174,c_34919])).

tff(c_22,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34972,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34918,c_22])).

tff(c_35215,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35181,c_34972])).

tff(c_6,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_31,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_34921,plain,(
    ! [A_723,B_724] : k9_subset_1(A_723,B_724,A_723) = k3_xboole_0(B_724,A_723) ),
    inference(resolution,[status(thm)],[c_31,c_34905])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34927,plain,(
    ! [B_724,A_723] :
      ( m1_subset_1(k3_xboole_0(B_724,A_723),k1_zfmisc_1(A_723))
      | ~ m1_subset_1(A_723,k1_zfmisc_1(A_723)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34921,c_10])).

tff(c_34935,plain,(
    ! [B_725,A_726] : m1_subset_1(k3_xboole_0(B_725,A_726),k1_zfmisc_1(A_726)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_34927])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34951,plain,(
    ! [B_725,A_726] : r1_tarski(k3_xboole_0(B_725,A_726),A_726) ),
    inference(resolution,[status(thm)],[c_34935,c_16])).

tff(c_35223,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_35181,c_34951])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35282,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_35223,c_2])).

tff(c_34842,plain,(
    ! [A_707,B_708] :
      ( r1_tarski(A_707,B_708)
      | ~ m1_subset_1(A_707,k1_zfmisc_1(B_708)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34854,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_31,c_34842])).

tff(c_34920,plain,(
    ! [A_7,B_721] : k9_subset_1(A_7,B_721,A_7) = k3_xboole_0(B_721,A_7) ),
    inference(resolution,[status(thm)],[c_31,c_34905])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_31,c_45])).

tff(c_106,plain,(
    ! [A_44,B_45,C_46] :
      ( k9_subset_1(A_44,B_45,C_46) = k3_xboole_0(B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [A_7,B_45] : k9_subset_1(A_7,B_45,A_7) = k3_xboole_0(B_45,A_7) ),
    inference(resolution,[status(thm)],[c_31,c_106])).

tff(c_24,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_41,B_42,C_43] :
      ( m1_subset_1(k9_subset_1(A_41,B_42,C_43),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_706,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(k9_subset_1(A_77,B_78,C_79),A_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_101,c_16])).

tff(c_2571,plain,(
    ! [A_139,B_140,C_141] :
      ( k3_xboole_0(k9_subset_1(A_139,B_140,C_141),A_139) = k9_subset_1(A_139,B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_706,c_2])).

tff(c_8403,plain,(
    ! [B_290,B_291,A_292] :
      ( k3_xboole_0(k9_subset_1(B_290,B_291,A_292),B_290) = k9_subset_1(B_290,B_291,A_292)
      | ~ r1_tarski(A_292,B_290) ) ),
    inference(resolution,[status(thm)],[c_18,c_2571])).

tff(c_255,plain,(
    ! [B_59] : k9_subset_1(u1_struct_0('#skF_1'),B_59,'#skF_2') = k3_xboole_0(B_59,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_106])).

tff(c_265,plain,(
    ! [B_59] :
      ( m1_subset_1(k3_xboole_0(B_59,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_10])).

tff(c_276,plain,(
    ! [B_59] : m1_subset_1(k3_xboole_0(B_59,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_265])).

tff(c_9396,plain,(
    ! [B_305,A_306] :
      ( m1_subset_1(k9_subset_1('#skF_2',B_305,A_306),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_306,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8403,c_276])).

tff(c_20,plain,(
    ! [C_24,A_18,B_22] :
      ( v2_tex_2(C_24,A_18)
      | ~ v2_tex_2(B_22,A_18)
      | ~ r1_tarski(C_24,B_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_733,plain,(
    ! [A_77,B_78,C_79,A_18] :
      ( v2_tex_2(k9_subset_1(A_77,B_78,C_79),A_18)
      | ~ v2_tex_2(A_77,A_18)
      | ~ m1_subset_1(k9_subset_1(A_77,B_78,C_79),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(A_77,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_706,c_20])).

tff(c_9399,plain,(
    ! [B_305,A_306] :
      ( v2_tex_2(k9_subset_1('#skF_2',B_305,A_306),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(A_306,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_306,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_9396,c_733])).

tff(c_34782,plain,(
    ! [B_705,A_706] :
      ( v2_tex_2(k9_subset_1('#skF_2',B_705,A_706),'#skF_1')
      | ~ m1_subset_1(A_706,k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski(A_706,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_42,c_9399])).

tff(c_34830,plain,(
    ! [B_45] :
      ( v2_tex_2(k3_xboole_0(B_45,'#skF_2'),'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
      | ~ r1_tarski('#skF_2','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_34782])).

tff(c_34836,plain,(
    ! [B_45] : v2_tex_2(k3_xboole_0(B_45,'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_31,c_34830])).

tff(c_119,plain,(
    ! [B_45] : k9_subset_1(u1_struct_0('#skF_1'),B_45,'#skF_3') = k3_xboole_0(B_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_188,plain,(
    ! [A_54,C_55,B_56] :
      ( k9_subset_1(A_54,C_55,B_56) = k9_subset_1(A_54,B_56,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_196,plain,(
    ! [B_56] : k9_subset_1(u1_struct_0('#skF_1'),B_56,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_56) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_375,plain,(
    ! [B_67] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_67) = k3_xboole_0(B_67,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_196])).

tff(c_120,plain,(
    ! [B_45] : k9_subset_1(u1_struct_0('#skF_1'),B_45,'#skF_2') = k3_xboole_0(B_45,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_106])).

tff(c_382,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_120])).

tff(c_173,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_22])).

tff(c_416,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_173])).

tff(c_34839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34836,c_416])).

tff(c_34840,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_34900,plain,(
    ! [A_717,B_718,C_719] :
      ( m1_subset_1(k9_subset_1(A_717,B_718,C_719),k1_zfmisc_1(A_717))
      | ~ m1_subset_1(C_719,k1_zfmisc_1(A_717)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35504,plain,(
    ! [A_753,B_754,C_755] :
      ( r1_tarski(k9_subset_1(A_753,B_754,C_755),A_753)
      | ~ m1_subset_1(C_755,k1_zfmisc_1(A_753)) ) ),
    inference(resolution,[status(thm)],[c_34900,c_16])).

tff(c_37341,plain,(
    ! [A_813,B_814,C_815] :
      ( k3_xboole_0(k9_subset_1(A_813,B_814,C_815),A_813) = k9_subset_1(A_813,B_814,C_815)
      | ~ m1_subset_1(C_815,k1_zfmisc_1(A_813)) ) ),
    inference(resolution,[status(thm)],[c_35504,c_2])).

tff(c_43431,plain,(
    ! [B_964,B_965,A_966] :
      ( k3_xboole_0(k9_subset_1(B_964,B_965,A_966),B_964) = k9_subset_1(B_964,B_965,A_966)
      | ~ r1_tarski(A_966,B_964) ) ),
    inference(resolution,[status(thm)],[c_18,c_37341])).

tff(c_34973,plain,(
    ! [B_729] : k9_subset_1(u1_struct_0('#skF_1'),B_729,'#skF_3') = k3_xboole_0(B_729,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_34905])).

tff(c_34979,plain,(
    ! [B_729] :
      ( m1_subset_1(k3_xboole_0(B_729,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34973,c_10])).

tff(c_34985,plain,(
    ! [B_729] : m1_subset_1(k3_xboole_0(B_729,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34979])).

tff(c_44461,plain,(
    ! [B_980,A_981] :
      ( m1_subset_1(k9_subset_1('#skF_3',B_980,A_981),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_981,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43431,c_34985])).

tff(c_35531,plain,(
    ! [A_753,B_754,C_755,A_18] :
      ( v2_tex_2(k9_subset_1(A_753,B_754,C_755),A_18)
      | ~ v2_tex_2(A_753,A_18)
      | ~ m1_subset_1(k9_subset_1(A_753,B_754,C_755),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ m1_subset_1(A_753,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18)
      | ~ m1_subset_1(C_755,k1_zfmisc_1(A_753)) ) ),
    inference(resolution,[status(thm)],[c_35504,c_20])).

tff(c_44464,plain,(
    ! [B_980,A_981] :
      ( v2_tex_2(k9_subset_1('#skF_3',B_980,A_981),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_subset_1(A_981,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_981,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44461,c_35531])).

tff(c_79766,plain,(
    ! [B_1501,A_1502] :
      ( v2_tex_2(k9_subset_1('#skF_3',B_1501,A_1502),'#skF_1')
      | ~ m1_subset_1(A_1502,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_1502,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_34840,c_44464])).

tff(c_79820,plain,(
    ! [B_721] :
      ( v2_tex_2(k3_xboole_0(B_721,'#skF_3'),'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski('#skF_3','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34920,c_79766])).

tff(c_79829,plain,(
    ! [B_1503] : v2_tex_2(k3_xboole_0(B_1503,'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34854,c_31,c_79820])).

tff(c_79857,plain,(
    v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_35282,c_79829])).

tff(c_79871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35215,c_79857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.12/15.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/15.28  
% 25.12/15.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/15.29  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 25.12/15.29  
% 25.12/15.29  %Foreground sorts:
% 25.12/15.29  
% 25.12/15.29  
% 25.12/15.29  %Background operators:
% 25.12/15.29  
% 25.12/15.29  
% 25.12/15.29  %Foreground operators:
% 25.12/15.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.12/15.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 25.12/15.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.12/15.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.12/15.29  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 25.12/15.29  tff('#skF_2', type, '#skF_2': $i).
% 25.12/15.29  tff('#skF_3', type, '#skF_3': $i).
% 25.12/15.29  tff('#skF_1', type, '#skF_1': $i).
% 25.12/15.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 25.12/15.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.12/15.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.12/15.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.12/15.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 25.12/15.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 25.12/15.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 25.12/15.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 25.12/15.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 25.12/15.29  
% 25.12/15.30  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 25.12/15.30  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 25.12/15.30  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 25.12/15.30  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 25.12/15.30  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 25.12/15.30  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 25.12/15.30  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 25.12/15.30  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 25.12/15.30  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 25.12/15.30  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/15.30  tff(c_34905, plain, (![A_720, B_721, C_722]: (k9_subset_1(A_720, B_721, C_722)=k3_xboole_0(B_721, C_722) | ~m1_subset_1(C_722, k1_zfmisc_1(A_720)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.12/15.31  tff(c_34918, plain, (![B_721]: (k9_subset_1(u1_struct_0('#skF_1'), B_721, '#skF_3')=k3_xboole_0(B_721, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_34905])).
% 25.12/15.31  tff(c_34987, plain, (![A_730, C_731, B_732]: (k9_subset_1(A_730, C_731, B_732)=k9_subset_1(A_730, B_732, C_731) | ~m1_subset_1(C_731, k1_zfmisc_1(A_730)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.12/15.31  tff(c_34995, plain, (![B_732]: (k9_subset_1(u1_struct_0('#skF_1'), B_732, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_732))), inference(resolution, [status(thm)], [c_26, c_34987])).
% 25.12/15.31  tff(c_35174, plain, (![B_743]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_743)=k3_xboole_0(B_743, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34918, c_34995])).
% 25.12/15.31  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/15.31  tff(c_34919, plain, (![B_721]: (k9_subset_1(u1_struct_0('#skF_1'), B_721, '#skF_2')=k3_xboole_0(B_721, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_34905])).
% 25.12/15.31  tff(c_35181, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35174, c_34919])).
% 25.12/15.31  tff(c_22, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/15.31  tff(c_34972, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34918, c_22])).
% 25.12/15.31  tff(c_35215, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35181, c_34972])).
% 25.12/15.31  tff(c_6, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 25.12/15.31  tff(c_8, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.12/15.31  tff(c_31, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 25.12/15.31  tff(c_34921, plain, (![A_723, B_724]: (k9_subset_1(A_723, B_724, A_723)=k3_xboole_0(B_724, A_723))), inference(resolution, [status(thm)], [c_31, c_34905])).
% 25.12/15.31  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.12/15.31  tff(c_34927, plain, (![B_724, A_723]: (m1_subset_1(k3_xboole_0(B_724, A_723), k1_zfmisc_1(A_723)) | ~m1_subset_1(A_723, k1_zfmisc_1(A_723)))), inference(superposition, [status(thm), theory('equality')], [c_34921, c_10])).
% 25.12/15.31  tff(c_34935, plain, (![B_725, A_726]: (m1_subset_1(k3_xboole_0(B_725, A_726), k1_zfmisc_1(A_726)))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_34927])).
% 25.12/15.31  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/15.31  tff(c_34951, plain, (![B_725, A_726]: (r1_tarski(k3_xboole_0(B_725, A_726), A_726))), inference(resolution, [status(thm)], [c_34935, c_16])).
% 25.12/15.31  tff(c_35223, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_35181, c_34951])).
% 25.12/15.31  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 25.12/15.31  tff(c_35282, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_35223, c_2])).
% 25.12/15.31  tff(c_34842, plain, (![A_707, B_708]: (r1_tarski(A_707, B_708) | ~m1_subset_1(A_707, k1_zfmisc_1(B_708)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/15.31  tff(c_34854, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_31, c_34842])).
% 25.12/15.31  tff(c_34920, plain, (![A_7, B_721]: (k9_subset_1(A_7, B_721, A_7)=k3_xboole_0(B_721, A_7))), inference(resolution, [status(thm)], [c_31, c_34905])).
% 25.12/15.31  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/15.31  tff(c_45, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/15.31  tff(c_61, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_31, c_45])).
% 25.12/15.31  tff(c_106, plain, (![A_44, B_45, C_46]: (k9_subset_1(A_44, B_45, C_46)=k3_xboole_0(B_45, C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 25.12/15.31  tff(c_121, plain, (![A_7, B_45]: (k9_subset_1(A_7, B_45, A_7)=k3_xboole_0(B_45, A_7))), inference(resolution, [status(thm)], [c_31, c_106])).
% 25.12/15.31  tff(c_24, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 25.12/15.31  tff(c_42, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 25.12/15.31  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 25.12/15.31  tff(c_101, plain, (![A_41, B_42, C_43]: (m1_subset_1(k9_subset_1(A_41, B_42, C_43), k1_zfmisc_1(A_41)) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.12/15.31  tff(c_706, plain, (![A_77, B_78, C_79]: (r1_tarski(k9_subset_1(A_77, B_78, C_79), A_77) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_101, c_16])).
% 25.12/15.31  tff(c_2571, plain, (![A_139, B_140, C_141]: (k3_xboole_0(k9_subset_1(A_139, B_140, C_141), A_139)=k9_subset_1(A_139, B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(A_139)))), inference(resolution, [status(thm)], [c_706, c_2])).
% 25.12/15.31  tff(c_8403, plain, (![B_290, B_291, A_292]: (k3_xboole_0(k9_subset_1(B_290, B_291, A_292), B_290)=k9_subset_1(B_290, B_291, A_292) | ~r1_tarski(A_292, B_290))), inference(resolution, [status(thm)], [c_18, c_2571])).
% 25.12/15.31  tff(c_255, plain, (![B_59]: (k9_subset_1(u1_struct_0('#skF_1'), B_59, '#skF_2')=k3_xboole_0(B_59, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_106])).
% 25.12/15.31  tff(c_265, plain, (![B_59]: (m1_subset_1(k3_xboole_0(B_59, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_255, c_10])).
% 25.12/15.31  tff(c_276, plain, (![B_59]: (m1_subset_1(k3_xboole_0(B_59, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_265])).
% 25.12/15.31  tff(c_9396, plain, (![B_305, A_306]: (m1_subset_1(k9_subset_1('#skF_2', B_305, A_306), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_306, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8403, c_276])).
% 25.12/15.31  tff(c_20, plain, (![C_24, A_18, B_22]: (v2_tex_2(C_24, A_18) | ~v2_tex_2(B_22, A_18) | ~r1_tarski(C_24, B_22) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 25.12/15.31  tff(c_733, plain, (![A_77, B_78, C_79, A_18]: (v2_tex_2(k9_subset_1(A_77, B_78, C_79), A_18) | ~v2_tex_2(A_77, A_18) | ~m1_subset_1(k9_subset_1(A_77, B_78, C_79), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(A_77, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_706, c_20])).
% 25.12/15.31  tff(c_9399, plain, (![B_305, A_306]: (v2_tex_2(k9_subset_1('#skF_2', B_305, A_306), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(A_306, k1_zfmisc_1('#skF_2')) | ~r1_tarski(A_306, '#skF_2'))), inference(resolution, [status(thm)], [c_9396, c_733])).
% 25.12/15.31  tff(c_34782, plain, (![B_705, A_706]: (v2_tex_2(k9_subset_1('#skF_2', B_705, A_706), '#skF_1') | ~m1_subset_1(A_706, k1_zfmisc_1('#skF_2')) | ~r1_tarski(A_706, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_42, c_9399])).
% 25.12/15.31  tff(c_34830, plain, (![B_45]: (v2_tex_2(k3_xboole_0(B_45, '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_121, c_34782])).
% 25.12/15.31  tff(c_34836, plain, (![B_45]: (v2_tex_2(k3_xboole_0(B_45, '#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_31, c_34830])).
% 25.12/15.31  tff(c_119, plain, (![B_45]: (k9_subset_1(u1_struct_0('#skF_1'), B_45, '#skF_3')=k3_xboole_0(B_45, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_106])).
% 25.12/15.31  tff(c_188, plain, (![A_54, C_55, B_56]: (k9_subset_1(A_54, C_55, B_56)=k9_subset_1(A_54, B_56, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 25.12/15.31  tff(c_196, plain, (![B_56]: (k9_subset_1(u1_struct_0('#skF_1'), B_56, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_56))), inference(resolution, [status(thm)], [c_26, c_188])).
% 25.12/15.31  tff(c_375, plain, (![B_67]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_67)=k3_xboole_0(B_67, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_196])).
% 25.12/15.31  tff(c_120, plain, (![B_45]: (k9_subset_1(u1_struct_0('#skF_1'), B_45, '#skF_2')=k3_xboole_0(B_45, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_106])).
% 25.12/15.31  tff(c_382, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_375, c_120])).
% 25.12/15.31  tff(c_173, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_22])).
% 25.12/15.31  tff(c_416, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_173])).
% 25.12/15.31  tff(c_34839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34836, c_416])).
% 25.12/15.31  tff(c_34840, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 25.12/15.31  tff(c_34900, plain, (![A_717, B_718, C_719]: (m1_subset_1(k9_subset_1(A_717, B_718, C_719), k1_zfmisc_1(A_717)) | ~m1_subset_1(C_719, k1_zfmisc_1(A_717)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 25.12/15.31  tff(c_35504, plain, (![A_753, B_754, C_755]: (r1_tarski(k9_subset_1(A_753, B_754, C_755), A_753) | ~m1_subset_1(C_755, k1_zfmisc_1(A_753)))), inference(resolution, [status(thm)], [c_34900, c_16])).
% 25.12/15.31  tff(c_37341, plain, (![A_813, B_814, C_815]: (k3_xboole_0(k9_subset_1(A_813, B_814, C_815), A_813)=k9_subset_1(A_813, B_814, C_815) | ~m1_subset_1(C_815, k1_zfmisc_1(A_813)))), inference(resolution, [status(thm)], [c_35504, c_2])).
% 25.12/15.31  tff(c_43431, plain, (![B_964, B_965, A_966]: (k3_xboole_0(k9_subset_1(B_964, B_965, A_966), B_964)=k9_subset_1(B_964, B_965, A_966) | ~r1_tarski(A_966, B_964))), inference(resolution, [status(thm)], [c_18, c_37341])).
% 25.12/15.31  tff(c_34973, plain, (![B_729]: (k9_subset_1(u1_struct_0('#skF_1'), B_729, '#skF_3')=k3_xboole_0(B_729, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_34905])).
% 25.12/15.31  tff(c_34979, plain, (![B_729]: (m1_subset_1(k3_xboole_0(B_729, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_34973, c_10])).
% 25.12/15.31  tff(c_34985, plain, (![B_729]: (m1_subset_1(k3_xboole_0(B_729, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34979])).
% 25.12/15.31  tff(c_44461, plain, (![B_980, A_981]: (m1_subset_1(k9_subset_1('#skF_3', B_980, A_981), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_981, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43431, c_34985])).
% 25.12/15.31  tff(c_35531, plain, (![A_753, B_754, C_755, A_18]: (v2_tex_2(k9_subset_1(A_753, B_754, C_755), A_18) | ~v2_tex_2(A_753, A_18) | ~m1_subset_1(k9_subset_1(A_753, B_754, C_755), k1_zfmisc_1(u1_struct_0(A_18))) | ~m1_subset_1(A_753, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18) | ~m1_subset_1(C_755, k1_zfmisc_1(A_753)))), inference(resolution, [status(thm)], [c_35504, c_20])).
% 25.12/15.31  tff(c_44464, plain, (![B_980, A_981]: (v2_tex_2(k9_subset_1('#skF_3', B_980, A_981), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~m1_subset_1(A_981, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_981, '#skF_3'))), inference(resolution, [status(thm)], [c_44461, c_35531])).
% 25.12/15.31  tff(c_79766, plain, (![B_1501, A_1502]: (v2_tex_2(k9_subset_1('#skF_3', B_1501, A_1502), '#skF_1') | ~m1_subset_1(A_1502, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_1502, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_34840, c_44464])).
% 25.12/15.31  tff(c_79820, plain, (![B_721]: (v2_tex_2(k3_xboole_0(B_721, '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34920, c_79766])).
% 25.12/15.31  tff(c_79829, plain, (![B_1503]: (v2_tex_2(k3_xboole_0(B_1503, '#skF_3'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34854, c_31, c_79820])).
% 25.12/15.31  tff(c_79857, plain, (v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_35282, c_79829])).
% 25.12/15.31  tff(c_79871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35215, c_79857])).
% 25.12/15.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.12/15.31  
% 25.12/15.31  Inference rules
% 25.12/15.31  ----------------------
% 25.12/15.31  #Ref     : 0
% 25.12/15.31  #Sup     : 20679
% 25.12/15.31  #Fact    : 0
% 25.12/15.31  #Define  : 0
% 25.12/15.31  #Split   : 2
% 25.12/15.31  #Chain   : 0
% 25.12/15.31  #Close   : 0
% 25.12/15.31  
% 25.12/15.31  Ordering : KBO
% 25.12/15.31  
% 25.12/15.31  Simplification rules
% 25.12/15.31  ----------------------
% 25.12/15.31  #Subsume      : 284
% 25.12/15.31  #Demod        : 15605
% 25.12/15.31  #Tautology    : 9587
% 25.12/15.31  #SimpNegUnit  : 3
% 25.12/15.31  #BackRed      : 17
% 25.12/15.31  
% 25.12/15.31  #Partial instantiations: 0
% 25.12/15.31  #Strategies tried      : 1
% 25.12/15.31  
% 25.12/15.31  Timing (in seconds)
% 25.12/15.31  ----------------------
% 25.12/15.31  Preprocessing        : 0.30
% 25.12/15.31  Parsing              : 0.16
% 25.12/15.31  CNF conversion       : 0.02
% 25.12/15.31  Main loop            : 14.22
% 25.12/15.31  Inferencing          : 1.97
% 25.46/15.31  Reduction            : 8.16
% 25.46/15.31  Demodulation         : 7.43
% 25.46/15.31  BG Simplification    : 0.30
% 25.46/15.31  Subsumption          : 3.10
% 25.46/15.31  Abstraction          : 0.47
% 25.46/15.31  MUC search           : 0.00
% 25.46/15.31  Cooper               : 0.00
% 25.46/15.31  Total                : 14.58
% 25.46/15.31  Index Insertion      : 0.00
% 25.46/15.31  Index Deletion       : 0.00
% 25.46/15.31  Index Matching       : 0.00
% 25.46/15.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
