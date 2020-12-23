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
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 257 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 704 expanded)
%              Number of equality atoms :   19 ( 110 expanded)
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

tff(f_81,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

tff(c_20,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,
    ( v2_compts_1('#skF_4','#skF_2')
    | v2_compts_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_39,plain,
    ( v2_compts_1('#skF_4','#skF_2')
    | v2_compts_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_36])).

tff(c_45,plain,(
    v2_compts_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_39])).

tff(c_30,plain,
    ( ~ v2_compts_1('#skF_5','#skF_3')
    | ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,
    ( ~ v2_compts_1('#skF_4','#skF_3')
    | ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_52,plain,(
    ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_38])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    ! [A_43] :
      ( u1_struct_0(A_43) = k2_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_57,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_24])).

tff(c_64,plain,(
    ! [B_46,A_47] :
      ( l1_pre_topc(B_46)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67])).

tff(c_50,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = k2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_87,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_50])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_71,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_71])).

tff(c_88,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_83])).

tff(c_99,plain,(
    ! [A_50,B_51,C_52] :
      ( '#skF_1'(A_50,B_51,C_52) = C_52
      | v2_compts_1(C_52,A_50)
      | ~ r1_tarski(C_52,k2_struct_0(B_51))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ m1_pre_topc(B_51,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,(
    ! [A_53] :
      ( '#skF_1'(A_53,'#skF_3','#skF_4') = '#skF_4'
      | v2_compts_1('#skF_4',A_53)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc('#skF_3',A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_88,c_99])).

tff(c_115,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_106])).

tff(c_120,plain,
    ( '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_58,c_115])).

tff(c_121,plain,(
    '#skF_1'('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_120])).

tff(c_126,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ v2_compts_1('#skF_1'(A_54,B_55,C_56),B_55)
      | v2_compts_1(C_56,A_54)
      | ~ r1_tarski(C_56,k2_struct_0(B_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_pre_topc(B_55,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,
    ( ~ v2_compts_1('#skF_4','#skF_3')
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_126])).

tff(c_130,plain,(
    v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_58,c_57,c_88,c_45,c_128])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_130])).

tff(c_134,plain,(
    ~ v2_compts_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_153,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_156,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_159,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_156])).

tff(c_137,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    ! [A_4] :
      ( u1_struct_0(A_4) = k2_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_137])).

tff(c_176,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_141])).

tff(c_160,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37,c_160])).

tff(c_177,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_172])).

tff(c_133,plain,(
    v2_compts_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_39])).

tff(c_142,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_8,c_137])).

tff(c_146,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_142])).

tff(c_147,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_254,plain,(
    ! [D_75,B_76,A_77] :
      ( v2_compts_1(D_75,B_76)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(B_76)))
      | ~ v2_compts_1(D_75,A_77)
      | ~ r1_tarski(D_75,k2_struct_0(B_76))
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_263,plain,(
    ! [A_78,B_79,A_80] :
      ( v2_compts_1(A_78,B_79)
      | ~ v2_compts_1(A_78,A_80)
      | ~ r1_tarski(A_78,k2_struct_0(B_79))
      | ~ m1_subset_1(A_78,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80)
      | ~ r1_tarski(A_78,u1_struct_0(B_79)) ) ),
    inference(resolution,[status(thm)],[c_4,c_254])).

tff(c_270,plain,(
    ! [A_78,B_79] :
      ( v2_compts_1(A_78,B_79)
      | ~ v2_compts_1(A_78,'#skF_2')
      | ~ r1_tarski(A_78,k2_struct_0(B_79))
      | ~ m1_subset_1(A_78,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_79,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_78,u1_struct_0(B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_263])).

tff(c_308,plain,(
    ! [A_88,B_89] :
      ( v2_compts_1(A_88,B_89)
      | ~ v2_compts_1(A_88,'#skF_2')
      | ~ r1_tarski(A_88,k2_struct_0(B_89))
      | ~ m1_subset_1(A_88,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ r1_tarski(A_88,u1_struct_0(B_89)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).

tff(c_313,plain,(
    ! [B_89] :
      ( v2_compts_1('#skF_4',B_89)
      | ~ v2_compts_1('#skF_4','#skF_2')
      | ~ r1_tarski('#skF_4',k2_struct_0(B_89))
      | ~ m1_pre_topc(B_89,'#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0(B_89)) ) ),
    inference(resolution,[status(thm)],[c_147,c_308])).

tff(c_318,plain,(
    ! [B_90] :
      ( v2_compts_1('#skF_4',B_90)
      | ~ r1_tarski('#skF_4',k2_struct_0(B_90))
      | ~ m1_pre_topc(B_90,'#skF_2')
      | ~ r1_tarski('#skF_4',u1_struct_0(B_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_313])).

tff(c_321,plain,
    ( v2_compts_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_318])).

tff(c_326,plain,(
    v2_compts_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_26,c_177,c_321])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  %$ v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.12/1.30  
% 2.12/1.30  %Foreground sorts:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Background operators:
% 2.12/1.30  
% 2.12/1.30  
% 2.12/1.30  %Foreground operators:
% 2.12/1.30  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.12/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.30  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.12/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.12/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.30  
% 2.12/1.31  tff(f_81, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((C = D) => (v2_compts_1(C, A) <=> v2_compts_1(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_compts_1)).
% 2.12/1.31  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.12/1.31  tff(f_33, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.12/1.31  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.12/1.31  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.12/1.31  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 2.12/1.31  tff(c_20, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_36, plain, (v2_compts_1('#skF_4', '#skF_2') | v2_compts_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_39, plain, (v2_compts_1('#skF_4', '#skF_2') | v2_compts_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_36])).
% 2.12/1.31  tff(c_45, plain, (v2_compts_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_39])).
% 2.12/1.31  tff(c_30, plain, (~v2_compts_1('#skF_5', '#skF_3') | ~v2_compts_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_38, plain, (~v2_compts_1('#skF_4', '#skF_3') | ~v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 2.12/1.31  tff(c_52, plain, (~v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_38])).
% 2.12/1.31  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.31  tff(c_46, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_53, plain, (![A_43]: (u1_struct_0(A_43)=k2_struct_0(A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_8, c_46])).
% 2.12/1.31  tff(c_57, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.12/1.31  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_24])).
% 2.12/1.31  tff(c_64, plain, (![B_46, A_47]: (l1_pre_topc(B_46) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.31  tff(c_67, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.12/1.31  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67])).
% 2.12/1.31  tff(c_50, plain, (![A_4]: (u1_struct_0(A_4)=k2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_46])).
% 2.12/1.31  tff(c_87, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_70, c_50])).
% 2.12/1.31  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.31  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.12/1.31  tff(c_71, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.31  tff(c_83, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_37, c_71])).
% 2.12/1.31  tff(c_88, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_83])).
% 2.12/1.31  tff(c_99, plain, (![A_50, B_51, C_52]: ('#skF_1'(A_50, B_51, C_52)=C_52 | v2_compts_1(C_52, A_50) | ~r1_tarski(C_52, k2_struct_0(B_51)) | ~m1_subset_1(C_52, k1_zfmisc_1(u1_struct_0(A_50))) | ~m1_pre_topc(B_51, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.31  tff(c_106, plain, (![A_53]: ('#skF_1'(A_53, '#skF_3', '#skF_4')='#skF_4' | v2_compts_1('#skF_4', A_53) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc('#skF_3', A_53) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_88, c_99])).
% 2.12/1.31  tff(c_115, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_106])).
% 2.12/1.31  tff(c_120, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_58, c_115])).
% 2.12/1.31  tff(c_121, plain, ('#skF_1'('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_120])).
% 2.12/1.31  tff(c_126, plain, (![A_54, B_55, C_56]: (~v2_compts_1('#skF_1'(A_54, B_55, C_56), B_55) | v2_compts_1(C_56, A_54) | ~r1_tarski(C_56, k2_struct_0(B_55)) | ~m1_subset_1(C_56, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_pre_topc(B_55, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.31  tff(c_128, plain, (~v2_compts_1('#skF_4', '#skF_3') | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_121, c_126])).
% 2.12/1.31  tff(c_130, plain, (v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_58, c_57, c_88, c_45, c_128])).
% 2.12/1.31  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_130])).
% 2.12/1.31  tff(c_134, plain, (~v2_compts_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_39])).
% 2.12/1.31  tff(c_153, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.31  tff(c_156, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_153])).
% 2.12/1.31  tff(c_159, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_156])).
% 2.12/1.31  tff(c_137, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.31  tff(c_141, plain, (![A_4]: (u1_struct_0(A_4)=k2_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_8, c_137])).
% 2.12/1.31  tff(c_176, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_159, c_141])).
% 2.12/1.31  tff(c_160, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.31  tff(c_172, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_37, c_160])).
% 2.12/1.31  tff(c_177, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_172])).
% 2.12/1.31  tff(c_133, plain, (v2_compts_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_39])).
% 2.12/1.31  tff(c_142, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_8, c_137])).
% 2.12/1.31  tff(c_146, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_142])).
% 2.12/1.31  tff(c_147, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_24])).
% 2.12/1.31  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.31  tff(c_254, plain, (![D_75, B_76, A_77]: (v2_compts_1(D_75, B_76) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(B_76))) | ~v2_compts_1(D_75, A_77) | ~r1_tarski(D_75, k2_struct_0(B_76)) | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.31  tff(c_263, plain, (![A_78, B_79, A_80]: (v2_compts_1(A_78, B_79) | ~v2_compts_1(A_78, A_80) | ~r1_tarski(A_78, k2_struct_0(B_79)) | ~m1_subset_1(A_78, k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80) | ~r1_tarski(A_78, u1_struct_0(B_79)))), inference(resolution, [status(thm)], [c_4, c_254])).
% 2.12/1.31  tff(c_270, plain, (![A_78, B_79]: (v2_compts_1(A_78, B_79) | ~v2_compts_1(A_78, '#skF_2') | ~r1_tarski(A_78, k2_struct_0(B_79)) | ~m1_subset_1(A_78, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_79, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_78, u1_struct_0(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_263])).
% 2.12/1.31  tff(c_308, plain, (![A_88, B_89]: (v2_compts_1(A_88, B_89) | ~v2_compts_1(A_88, '#skF_2') | ~r1_tarski(A_88, k2_struct_0(B_89)) | ~m1_subset_1(A_88, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_89, '#skF_2') | ~r1_tarski(A_88, u1_struct_0(B_89)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_270])).
% 2.12/1.31  tff(c_313, plain, (![B_89]: (v2_compts_1('#skF_4', B_89) | ~v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0(B_89)) | ~m1_pre_topc(B_89, '#skF_2') | ~r1_tarski('#skF_4', u1_struct_0(B_89)))), inference(resolution, [status(thm)], [c_147, c_308])).
% 2.12/1.31  tff(c_318, plain, (![B_90]: (v2_compts_1('#skF_4', B_90) | ~r1_tarski('#skF_4', k2_struct_0(B_90)) | ~m1_pre_topc(B_90, '#skF_2') | ~r1_tarski('#skF_4', u1_struct_0(B_90)))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_313])).
% 2.12/1.31  tff(c_321, plain, (v2_compts_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_318])).
% 2.12/1.31  tff(c_326, plain, (v2_compts_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_26, c_177, c_321])).
% 2.12/1.31  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_326])).
% 2.12/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  Inference rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Ref     : 0
% 2.12/1.31  #Sup     : 65
% 2.12/1.31  #Fact    : 0
% 2.12/1.31  #Define  : 0
% 2.12/1.31  #Split   : 3
% 2.12/1.31  #Chain   : 0
% 2.12/1.31  #Close   : 0
% 2.12/1.31  
% 2.12/1.31  Ordering : KBO
% 2.12/1.31  
% 2.12/1.31  Simplification rules
% 2.12/1.31  ----------------------
% 2.12/1.31  #Subsume      : 7
% 2.12/1.31  #Demod        : 55
% 2.12/1.31  #Tautology    : 23
% 2.12/1.31  #SimpNegUnit  : 7
% 2.12/1.31  #BackRed      : 6
% 2.12/1.31  
% 2.12/1.31  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.32  Preprocessing        : 0.30
% 2.12/1.32  Parsing              : 0.16
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.24
% 2.12/1.32  Inferencing          : 0.09
% 2.12/1.32  Reduction            : 0.07
% 2.12/1.32  Demodulation         : 0.05
% 2.12/1.32  BG Simplification    : 0.01
% 2.12/1.32  Subsumption          : 0.05
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.58
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
