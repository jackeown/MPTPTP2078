%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1373+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:52 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 251 expanded)
%              Number of leaves         :   23 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 684 expanded)
%              Number of equality atoms :   19 ( 107 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( C = D
                     => ( v2_compts_1(C,A)
                      <=> v2_compts_1(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_20,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,
    ( ~ v2_compts_1('#skF_5','#skF_3')
    | ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,
    ( ~ v2_compts_1('#skF_4','#skF_3')
    | ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_45,plain,(
    ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_52,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_47])).

tff(c_56,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_76,plain,(
    ! [B_48,A_49] :
      ( l1_pre_topc(B_48)
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_79])).

tff(c_51,plain,(
    ! [A_2] :
      ( u1_struct_0(A_2) = k2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_47])).

tff(c_86,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_51])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_62,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_62])).

tff(c_87,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_70])).

tff(c_36,plain,
    ( v2_compts_1('#skF_4','#skF_2')
    | v2_compts_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39,plain,
    ( v2_compts_1('#skF_4','#skF_2')
    | v2_compts_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_46,plain,(
    v2_compts_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_39])).

tff(c_98,plain,(
    ! [A_50,B_51,C_52] :
      ( '#skF_1'(A_50,B_51,C_52) = C_52
      | v2_compts_1(C_52,A_50)
      | ~ r1_tarski(C_52,k2_struct_0(B_51))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_51,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [A_53] :
      ( '#skF_1'(A_53,'#skF_3','#skF_4') = '#skF_4'
      | v2_compts_1('#skF_4',A_53)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc('#skF_3',A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_87,c_98])).

tff(c_114,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_105])).

tff(c_119,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_57,c_114])).

tff(c_120,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_119])).

tff(c_125,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ v2_compts_1('#skF_1'(A_54,B_55,C_56),B_55)
      | v2_compts_1(C_56,A_54)
      | ~ r1_tarski(C_56,k2_struct_0(B_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(B_55,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_127,plain,
    ( ~ v2_compts_1('#skF_4','#skF_3')
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_125])).

tff(c_129,plain,(
    v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_57,c_56,c_87,c_46,c_127])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_129])).

tff(c_132,plain,(
    ~ v2_compts_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_165,plain,(
    ! [B_63,A_64] :
      ( l1_pre_topc(B_63)
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_168,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_171,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_168])).

tff(c_134,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_138,plain,(
    ! [A_2] :
      ( u1_struct_0(A_2) = k2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_175,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_138])).

tff(c_151,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_159,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_151])).

tff(c_176,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_159])).

tff(c_133,plain,(
    v2_compts_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_141,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_134])).

tff(c_145,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_141])).

tff(c_146,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_24])).

tff(c_18,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_253,plain,(
    ! [D_75,B_76,A_77] :
      ( v2_compts_1(D_75,B_76)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ v2_compts_1(D_75,A_77)
      | ~ r1_tarski(D_75,k2_struct_0(B_76))
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_262,plain,(
    ! [A_78,B_79,A_80] :
      ( v2_compts_1(A_78,B_79)
      | ~ v2_compts_1(A_78,A_80)
      | ~ r1_tarski(A_78,k2_struct_0(B_79))
      | ~ m1_subset_1(A_78,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80)
      | ~ r1_tarski(A_78,u1_struct_0(B_79)) ) ),
    inference(resolution,[status(thm)],[c_18,c_253])).

tff(c_269,plain,(
    ! [A_78,B_79] :
      ( v2_compts_1(A_78,B_79)
      | ~ v2_compts_1(A_78,'#skF_2')
      | ~ r1_tarski(A_78,k2_struct_0(B_79))
      | ~ m1_subset_1(A_78,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_79,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_78,u1_struct_0(B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_262])).

tff(c_307,plain,(
    ! [A_88,B_89] :
      ( v2_compts_1(A_88,B_89)
      | ~ v2_compts_1(A_88,'#skF_2')
      | ~ r1_tarski(A_88,k2_struct_0(B_89))
      | ~ m1_subset_1(A_88,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ r1_tarski(A_88,u1_struct_0(B_89)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_269])).

tff(c_312,plain,(
    ! [B_89] :
      ( v2_compts_1('#skF_4',B_89)
      | ~ v2_compts_1('#skF_4','#skF_2')
      | ~ r1_tarski('#skF_4',k2_struct_0(B_89))
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0(B_89)) ) ),
    inference(resolution,[status(thm)],[c_146,c_307])).

tff(c_317,plain,(
    ! [B_90] :
      ( v2_compts_1('#skF_4',B_90)
      | ~ r1_tarski('#skF_4',k2_struct_0(B_90))
      | ~ m1_pre_topc(B_90,'#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0(B_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_312])).

tff(c_320,plain,
    ( v2_compts_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_317])).

tff(c_325,plain,(
    v2_compts_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_26,c_176,c_320])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_325])).

%------------------------------------------------------------------------------
