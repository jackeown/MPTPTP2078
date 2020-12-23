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
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 244 expanded)
%              Number of leaves         :   23 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  187 ( 634 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(c_32,plain,
    ( ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_39,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_2'(A_48,B_49),B_49)
      | v1_tops_2(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48))))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_87,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_80])).

tff(c_92,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_87])).

tff(c_93,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_92])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),A_50)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_93,c_2])).

tff(c_106,plain,(
    ! [A_51,A_52] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),A_51)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_51))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_115,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_106])).

tff(c_116,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_197,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),B_71)
      | r1_tarski(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_211,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_220,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_211])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_220])).

tff(c_229,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_10,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_244,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_10])).

tff(c_38,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_38])).

tff(c_255,plain,(
    ! [B_80,A_81] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),B_80)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_81))
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_275,plain,(
    ! [B_83,B_84] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),B_83)
      | ~ r1_tarski(B_84,B_83)
      | ~ r1_tarski('#skF_4',B_84) ) ),
    inference(resolution,[status(thm)],[c_12,c_255])).

tff(c_283,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_275])).

tff(c_293,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_283])).

tff(c_58,plain,(
    ! [B_38,A_39] :
      ( v3_pre_topc(B_38,A_39)
      | ~ r2_hidden(B_38,u1_pre_topc(A_39))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    ! [A_12,A_39] :
      ( v3_pre_topc(A_12,A_39)
      | ~ r2_hidden(A_12,u1_pre_topc(A_39))
      | ~ l1_pre_topc(A_39)
      | ~ r1_tarski(A_12,u1_struct_0(A_39)) ) ),
    inference(resolution,[status(thm)],[c_12,c_58])).

tff(c_296,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_293,c_63])).

tff(c_301,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_296])).

tff(c_377,plain,(
    ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_490,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1('#skF_2'(A_111,B_112),k1_zfmisc_1(u1_struct_0(A_111)))
      | v1_tops_2(B_112,A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111))))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_515,plain,(
    ! [A_113,B_114] :
      ( r1_tarski('#skF_2'(A_113,B_114),u1_struct_0(A_113))
      | v1_tops_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113))))
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_490,c_10])).

tff(c_525,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_515])).

tff(c_531,plain,
    ( r1_tarski('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_525])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_377,c_531])).

tff(c_534,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_22,plain,(
    ! [A_18,B_24] :
      ( ~ v3_pre_topc('#skF_2'(A_18,B_24),A_18)
      | v1_tops_2(B_24,A_18)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18))))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_537,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_534,c_22])).

tff(c_540,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_537])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_540])).

tff(c_543,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_544,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_18,plain,(
    ! [A_17] :
      ( m1_subset_1(u1_pre_topc(A_17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17))))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_743,plain,(
    ! [C_166,A_167,B_168] :
      ( v3_pre_topc(C_166,A_167)
      | ~ r2_hidden(C_166,B_168)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ v1_tops_2(B_168,A_167)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_167))))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1146,plain,(
    ! [A_272,B_273,C_274,A_275] :
      ( v3_pre_topc('#skF_1'(A_272,B_273,C_274),A_275)
      | ~ m1_subset_1('#skF_1'(A_272,B_273,C_274),k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ v1_tops_2(B_273,A_275)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_275))))
      | ~ l1_pre_topc(A_275)
      | r1_tarski(B_273,C_274)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(A_272))
      | ~ m1_subset_1(B_273,k1_zfmisc_1(A_272)) ) ),
    inference(resolution,[status(thm)],[c_6,c_743])).

tff(c_1429,plain,(
    ! [A_370,B_371,C_372] :
      ( v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_370)),B_371,C_372),A_370)
      | ~ v1_tops_2(B_371,A_370)
      | ~ l1_pre_topc(A_370)
      | r1_tarski(B_371,C_372)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_370))))
      | ~ m1_subset_1(B_371,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_370)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_1146])).

tff(c_624,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1('#skF_1'(A_142,B_143,C_144),A_142)
      | r1_tarski(B_143,C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,u1_pre_topc(A_14))
      | ~ v3_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1021,plain,(
    ! [A_244,B_245,C_246] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)),B_245,C_246),u1_pre_topc(A_244))
      | ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)),B_245,C_246),A_244)
      | ~ l1_pre_topc(A_244)
      | r1_tarski(B_245,C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244))))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))) ) ),
    inference(resolution,[status(thm)],[c_624,c_16])).

tff(c_1038,plain,(
    ! [A_244,B_245] :
      ( ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)),B_245,u1_pre_topc(A_244)),A_244)
      | ~ l1_pre_topc(A_244)
      | r1_tarski(B_245,u1_pre_topc(A_244))
      | ~ m1_subset_1(u1_pre_topc(A_244),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244))))
      | ~ m1_subset_1(B_245,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))) ) ),
    inference(resolution,[status(thm)],[c_1021,c_4])).

tff(c_1441,plain,(
    ! [B_376,A_377] :
      ( ~ v1_tops_2(B_376,A_377)
      | ~ l1_pre_topc(A_377)
      | r1_tarski(B_376,u1_pre_topc(A_377))
      | ~ m1_subset_1(u1_pre_topc(A_377),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377))))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377)))) ) ),
    inference(resolution,[status(thm)],[c_1429,c_1038])).

tff(c_1449,plain,(
    ! [B_378,A_379] :
      ( ~ v1_tops_2(B_378,A_379)
      | r1_tarski(B_378,u1_pre_topc(A_379))
      | ~ m1_subset_1(B_378,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_379))))
      | ~ l1_pre_topc(A_379) ) ),
    inference(resolution,[status(thm)],[c_18,c_1441])).

tff(c_1463,plain,
    ( ~ v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1449])).

tff(c_1469,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_544,c_1463])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_1469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  
% 4.37/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.37/1.76  
% 4.37/1.76  %Foreground sorts:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Background operators:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Foreground operators:
% 4.37/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.37/1.76  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.37/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.76  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.37/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.37/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.76  
% 4.51/1.78  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 4.51/1.78  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.51/1.78  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 4.51/1.78  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.51/1.78  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 4.51/1.78  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.51/1.78  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.51/1.78  tff(c_32, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~v1_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.78  tff(c_39, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 4.51/1.78  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.78  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.78  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.78  tff(c_80, plain, (![A_48, B_49]: (r2_hidden('#skF_2'(A_48, B_49), B_49) | v1_tops_2(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_48)))) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.78  tff(c_87, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_80])).
% 4.51/1.78  tff(c_92, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_87])).
% 4.51/1.78  tff(c_93, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_39, c_92])).
% 4.51/1.78  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.78  tff(c_97, plain, (![A_50]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), A_50) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_93, c_2])).
% 4.51/1.78  tff(c_106, plain, (![A_51, A_52]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), A_51) | ~m1_subset_1(A_52, k1_zfmisc_1(A_51)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_97, c_2])).
% 4.51/1.78  tff(c_115, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_106])).
% 4.51/1.78  tff(c_116, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_115])).
% 4.51/1.78  tff(c_120, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_116])).
% 4.51/1.78  tff(c_197, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), B_71) | r1_tarski(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_4, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_211, plain, (![B_73, A_74]: (r1_tarski(B_73, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_197, c_4])).
% 4.51/1.78  tff(c_220, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_211])).
% 4.51/1.78  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_220])).
% 4.51/1.78  tff(c_229, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_115])).
% 4.51/1.78  tff(c_10, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.78  tff(c_244, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_229, c_10])).
% 4.51/1.78  tff(c_38, plain, (v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.51/1.78  tff(c_40, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_39, c_38])).
% 4.51/1.78  tff(c_255, plain, (![B_80, A_81]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), B_80) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_81)) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_12, c_106])).
% 4.51/1.78  tff(c_275, plain, (![B_83, B_84]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), B_83) | ~r1_tarski(B_84, B_83) | ~r1_tarski('#skF_4', B_84))), inference(resolution, [status(thm)], [c_12, c_255])).
% 4.51/1.78  tff(c_283, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_275])).
% 4.51/1.78  tff(c_293, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_283])).
% 4.51/1.78  tff(c_58, plain, (![B_38, A_39]: (v3_pre_topc(B_38, A_39) | ~r2_hidden(B_38, u1_pre_topc(A_39)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.51/1.78  tff(c_63, plain, (![A_12, A_39]: (v3_pre_topc(A_12, A_39) | ~r2_hidden(A_12, u1_pre_topc(A_39)) | ~l1_pre_topc(A_39) | ~r1_tarski(A_12, u1_struct_0(A_39)))), inference(resolution, [status(thm)], [c_12, c_58])).
% 4.51/1.78  tff(c_296, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_293, c_63])).
% 4.51/1.78  tff(c_301, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_296])).
% 4.51/1.78  tff(c_377, plain, (~r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_301])).
% 4.51/1.78  tff(c_490, plain, (![A_111, B_112]: (m1_subset_1('#skF_2'(A_111, B_112), k1_zfmisc_1(u1_struct_0(A_111))) | v1_tops_2(B_112, A_111) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111)))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.78  tff(c_515, plain, (![A_113, B_114]: (r1_tarski('#skF_2'(A_113, B_114), u1_struct_0(A_113)) | v1_tops_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113)))) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_490, c_10])).
% 4.51/1.78  tff(c_525, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_515])).
% 4.51/1.78  tff(c_531, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_525])).
% 4.51/1.78  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_377, c_531])).
% 4.51/1.78  tff(c_534, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_301])).
% 4.51/1.78  tff(c_22, plain, (![A_18, B_24]: (~v3_pre_topc('#skF_2'(A_18, B_24), A_18) | v1_tops_2(B_24, A_18) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_18)))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.78  tff(c_537, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_534, c_22])).
% 4.51/1.78  tff(c_540, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_537])).
% 4.51/1.78  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_540])).
% 4.51/1.78  tff(c_543, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 4.51/1.78  tff(c_544, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 4.51/1.78  tff(c_18, plain, (![A_17]: (m1_subset_1(u1_pre_topc(A_17), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_17)))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.51/1.78  tff(c_8, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_6, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_743, plain, (![C_166, A_167, B_168]: (v3_pre_topc(C_166, A_167) | ~r2_hidden(C_166, B_168) | ~m1_subset_1(C_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~v1_tops_2(B_168, A_167) | ~m1_subset_1(B_168, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_167)))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.78  tff(c_1146, plain, (![A_272, B_273, C_274, A_275]: (v3_pre_topc('#skF_1'(A_272, B_273, C_274), A_275) | ~m1_subset_1('#skF_1'(A_272, B_273, C_274), k1_zfmisc_1(u1_struct_0(A_275))) | ~v1_tops_2(B_273, A_275) | ~m1_subset_1(B_273, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_275)))) | ~l1_pre_topc(A_275) | r1_tarski(B_273, C_274) | ~m1_subset_1(C_274, k1_zfmisc_1(A_272)) | ~m1_subset_1(B_273, k1_zfmisc_1(A_272)))), inference(resolution, [status(thm)], [c_6, c_743])).
% 4.51/1.78  tff(c_1429, plain, (![A_370, B_371, C_372]: (v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_370)), B_371, C_372), A_370) | ~v1_tops_2(B_371, A_370) | ~l1_pre_topc(A_370) | r1_tarski(B_371, C_372) | ~m1_subset_1(C_372, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_370)))) | ~m1_subset_1(B_371, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_370)))))), inference(resolution, [status(thm)], [c_8, c_1146])).
% 4.51/1.78  tff(c_624, plain, (![A_142, B_143, C_144]: (m1_subset_1('#skF_1'(A_142, B_143, C_144), A_142) | r1_tarski(B_143, C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.78  tff(c_16, plain, (![B_16, A_14]: (r2_hidden(B_16, u1_pre_topc(A_14)) | ~v3_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.51/1.78  tff(c_1021, plain, (![A_244, B_245, C_246]: (r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)), B_245, C_246), u1_pre_topc(A_244)) | ~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)), B_245, C_246), A_244) | ~l1_pre_topc(A_244) | r1_tarski(B_245, C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))) | ~m1_subset_1(B_245, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))))), inference(resolution, [status(thm)], [c_624, c_16])).
% 4.51/1.78  tff(c_1038, plain, (![A_244, B_245]: (~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_244)), B_245, u1_pre_topc(A_244)), A_244) | ~l1_pre_topc(A_244) | r1_tarski(B_245, u1_pre_topc(A_244)) | ~m1_subset_1(u1_pre_topc(A_244), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))) | ~m1_subset_1(B_245, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_244)))))), inference(resolution, [status(thm)], [c_1021, c_4])).
% 4.51/1.78  tff(c_1441, plain, (![B_376, A_377]: (~v1_tops_2(B_376, A_377) | ~l1_pre_topc(A_377) | r1_tarski(B_376, u1_pre_topc(A_377)) | ~m1_subset_1(u1_pre_topc(A_377), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377)))) | ~m1_subset_1(B_376, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_377)))))), inference(resolution, [status(thm)], [c_1429, c_1038])).
% 4.51/1.78  tff(c_1449, plain, (![B_378, A_379]: (~v1_tops_2(B_378, A_379) | r1_tarski(B_378, u1_pre_topc(A_379)) | ~m1_subset_1(B_378, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_379)))) | ~l1_pre_topc(A_379))), inference(resolution, [status(thm)], [c_18, c_1441])).
% 4.51/1.78  tff(c_1463, plain, (~v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1449])).
% 4.51/1.78  tff(c_1469, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_544, c_1463])).
% 4.51/1.78  tff(c_1471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_1469])).
% 4.51/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  Inference rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Ref     : 0
% 4.51/1.78  #Sup     : 324
% 4.51/1.78  #Fact    : 0
% 4.51/1.78  #Define  : 0
% 4.51/1.78  #Split   : 4
% 4.51/1.78  #Chain   : 0
% 4.51/1.78  #Close   : 0
% 4.51/1.78  
% 4.51/1.78  Ordering : KBO
% 4.51/1.78  
% 4.51/1.78  Simplification rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Subsume      : 50
% 4.51/1.78  #Demod        : 57
% 4.51/1.78  #Tautology    : 39
% 4.51/1.78  #SimpNegUnit  : 10
% 4.51/1.78  #BackRed      : 0
% 4.51/1.78  
% 4.51/1.78  #Partial instantiations: 0
% 4.51/1.78  #Strategies tried      : 1
% 4.51/1.78  
% 4.51/1.78  Timing (in seconds)
% 4.51/1.78  ----------------------
% 4.51/1.78  Preprocessing        : 0.30
% 4.51/1.78  Parsing              : 0.16
% 4.51/1.78  CNF conversion       : 0.02
% 4.51/1.78  Main loop            : 0.70
% 4.51/1.78  Inferencing          : 0.25
% 4.51/1.78  Reduction            : 0.16
% 4.51/1.78  Demodulation         : 0.10
% 4.51/1.78  BG Simplification    : 0.03
% 4.51/1.78  Subsumption          : 0.20
% 4.51/1.78  Abstraction          : 0.02
% 4.51/1.78  MUC search           : 0.00
% 4.51/1.78  Cooper               : 0.00
% 4.51/1.78  Total                : 1.04
% 4.51/1.78  Index Insertion      : 0.00
% 4.51/1.79  Index Deletion       : 0.00
% 4.51/1.79  Index Matching       : 0.00
% 4.51/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
