%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1354+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 9.49s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 345 expanded)
%              Number of leaves         :   30 ( 124 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 ( 873 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
            <=> r1_tarski(B,k7_setfam_1(u1_struct_0(A),u1_pre_topc(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_70,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    ! [A_34] :
      ( m1_subset_1(u1_pre_topc(A_34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),A_11)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_2'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_11] : r1_tarski(A_11,A_11) ),
    inference(resolution,[status(thm)],[c_14,c_58])).

tff(c_56,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_71,plain,(
    r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_56])).

tff(c_270,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_1'(A_107,B_108),B_108)
      | v2_tops_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_107))))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_280,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_270])).

tff(c_286,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_280])).

tff(c_287,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_286])).

tff(c_10,plain,(
    ! [C_15,B_12,A_11] :
      ( r2_hidden(C_15,B_12)
      | ~ r2_hidden(C_15,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_300,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_5'),B_109)
      | ~ r1_tarski('#skF_5',B_109) ) ),
    inference(resolution,[status(thm)],[c_287,c_10])).

tff(c_341,plain,(
    ! [B_113,B_114] :
      ( r2_hidden('#skF_1'('#skF_4','#skF_5'),B_113)
      | ~ r1_tarski(B_114,B_113)
      | ~ r1_tarski('#skF_5',B_114) ) ),
    inference(resolution,[status(thm)],[c_300,c_10])).

tff(c_345,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_341])).

tff(c_351,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_345])).

tff(c_103,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k7_setfam_1(A_62,B_63),k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [A_38,C_40,B_39] :
      ( m1_subset_1(A_38,C_40)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_106,plain,(
    ! [A_38,A_62,B_63] :
      ( m1_subset_1(A_38,k1_zfmisc_1(A_62))
      | ~ r2_hidden(A_38,k7_setfam_1(A_62,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(resolution,[status(thm)],[c_103,c_44])).

tff(c_361,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_351,c_106])).

tff(c_434,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_445,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_434])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_445])).

tff(c_450,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_451,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k7_setfam_1(A_32,B_33),k1_zfmisc_1(k1_zfmisc_1(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_800,plain,(
    ! [A_169,D_170,B_171] :
      ( r2_hidden(k3_subset_1(A_169,D_170),B_171)
      | ~ r2_hidden(D_170,k7_setfam_1(A_169,B_171))
      | ~ m1_subset_1(D_170,k1_zfmisc_1(A_169))
      | ~ m1_subset_1(k7_setfam_1(A_169,B_171),k1_zfmisc_1(k1_zfmisc_1(A_169)))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1159,plain,(
    ! [A_220,D_221,B_222] :
      ( r2_hidden(k3_subset_1(A_220,D_221),B_222)
      | ~ r2_hidden(D_221,k7_setfam_1(A_220,B_222))
      | ~ m1_subset_1(D_221,k1_zfmisc_1(A_220))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(k1_zfmisc_1(A_220))) ) ),
    inference(resolution,[status(thm)],[c_36,c_800])).

tff(c_1615,plain,(
    ! [D_261] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_261),u1_pre_topc('#skF_4'))
      | ~ r2_hidden(D_261,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_451,c_1159])).

tff(c_73,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_81,plain,(
    ! [A_53,A_34] :
      ( m1_subset_1(A_53,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ r2_hidden(A_53,u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_139,plain,(
    ! [B_77,A_78] :
      ( v3_pre_topc(B_77,A_78)
      | ~ r2_hidden(B_77,u1_pre_topc(A_78))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_150,plain,(
    ! [A_53,A_34] :
      ( v3_pre_topc(A_53,A_34)
      | ~ r2_hidden(A_53,u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_81,c_139])).

tff(c_1639,plain,(
    ! [D_261] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_261),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_261,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1(D_261,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1615,c_150])).

tff(c_1731,plain,(
    ! [D_266] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_266),'#skF_4')
      | ~ r2_hidden(D_266,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1(D_266,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1639])).

tff(c_1750,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_4','#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_351,c_1731])).

tff(c_1774,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_4','#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_1750])).

tff(c_40,plain,(
    ! [B_37,A_35] :
      ( v4_pre_topc(B_37,A_35)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_35),B_37),A_35)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1811,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1774,c_40])).

tff(c_1817,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_450,c_1811])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v4_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v2_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1819,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1817,c_4])).

tff(c_1822,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1819])).

tff(c_1824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1822])).

tff(c_1825,plain,(
    ~ r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_66,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    ! [A_11,B_12,B_49] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_49)
      | ~ r1_tarski(A_11,B_49)
      | r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_1826,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1827,plain,(
    ! [A_268,C_269,B_270] :
      ( m1_subset_1(A_268,C_269)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(C_269))
      | ~ r2_hidden(A_268,B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1833,plain,(
    ! [A_268] :
      ( m1_subset_1(A_268,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_268,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_1827])).

tff(c_2231,plain,(
    ! [C_368,A_369,B_370] :
      ( v4_pre_topc(C_368,A_369)
      | ~ r2_hidden(C_368,B_370)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ v2_tops_2(B_370,A_369)
      | ~ m1_subset_1(B_370,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_369))))
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3152,plain,(
    ! [A_519,B_520,A_521] :
      ( v4_pre_topc('#skF_2'(A_519,B_520),A_521)
      | ~ m1_subset_1('#skF_2'(A_519,B_520),k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ v2_tops_2(A_519,A_521)
      | ~ m1_subset_1(A_519,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_521))))
      | ~ l1_pre_topc(A_521)
      | r1_tarski(A_519,B_520) ) ),
    inference(resolution,[status(thm)],[c_14,c_2231])).

tff(c_3178,plain,(
    ! [A_519,B_520] :
      ( v4_pre_topc('#skF_2'(A_519,B_520),'#skF_4')
      | ~ v2_tops_2(A_519,'#skF_4')
      | ~ m1_subset_1(A_519,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | r1_tarski(A_519,B_520)
      | ~ r2_hidden('#skF_2'(A_519,B_520),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1833,c_3152])).

tff(c_3190,plain,(
    ! [A_522,B_523] :
      ( v4_pre_topc('#skF_2'(A_522,B_523),'#skF_4')
      | ~ v2_tops_2(A_522,'#skF_4')
      | ~ m1_subset_1(A_522,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | r1_tarski(A_522,B_523)
      | ~ r2_hidden('#skF_2'(A_522,B_523),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3178])).

tff(c_3213,plain,(
    ! [B_523] :
      ( v4_pre_topc('#skF_2'('#skF_5',B_523),'#skF_4')
      | ~ v2_tops_2('#skF_5','#skF_4')
      | r1_tarski('#skF_5',B_523)
      | ~ r2_hidden('#skF_2'('#skF_5',B_523),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_3190])).

tff(c_3225,plain,(
    ! [B_523] :
      ( v4_pre_topc('#skF_2'('#skF_5',B_523),'#skF_4')
      | r1_tarski('#skF_5',B_523)
      | ~ r2_hidden('#skF_2'('#skF_5',B_523),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1826,c_3213])).

tff(c_42,plain,(
    ! [A_35,B_37] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_35),B_37),A_35)
      | ~ v4_pre_topc(B_37,A_35)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1935,plain,(
    ! [B_301,A_302] :
      ( r2_hidden(B_301,u1_pre_topc(A_302))
      | ~ v3_pre_topc(B_301,A_302)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2339,plain,(
    ! [A_387,B_388] :
      ( r2_hidden(k3_subset_1(u1_struct_0(A_387),B_388),u1_pre_topc(A_387))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_387),B_388),A_387)
      | ~ l1_pre_topc(A_387)
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_387))) ) ),
    inference(resolution,[status(thm)],[c_34,c_1935])).

tff(c_2911,plain,(
    ! [A_476,B_477,B_478] :
      ( r2_hidden(k3_subset_1(u1_struct_0(A_476),B_477),B_478)
      | ~ r1_tarski(u1_pre_topc(A_476),B_478)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_476),B_477),A_476)
      | ~ l1_pre_topc(A_476)
      | ~ m1_subset_1(B_477,k1_zfmisc_1(u1_struct_0(A_476))) ) ),
    inference(resolution,[status(thm)],[c_2339,c_10])).

tff(c_2915,plain,(
    ! [A_479,B_480,B_481] :
      ( r2_hidden(k3_subset_1(u1_struct_0(A_479),B_480),B_481)
      | ~ r1_tarski(u1_pre_topc(A_479),B_481)
      | ~ v4_pre_topc(B_480,A_479)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ l1_pre_topc(A_479) ) ),
    inference(resolution,[status(thm)],[c_42,c_2911])).

tff(c_1832,plain,(
    ! [A_268,A_34] :
      ( m1_subset_1(A_268,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ r2_hidden(A_268,u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_1827])).

tff(c_1887,plain,(
    ! [B_291,A_292] :
      ( v3_pre_topc(B_291,A_292)
      | ~ r2_hidden(B_291,u1_pre_topc(A_292))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1898,plain,(
    ! [A_268,A_34] :
      ( v3_pre_topc(A_268,A_34)
      | ~ r2_hidden(A_268,u1_pre_topc(A_34))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_1832,c_1887])).

tff(c_2989,plain,(
    ! [A_479,B_480,A_34] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_479),B_480),A_34)
      | ~ l1_pre_topc(A_34)
      | ~ r1_tarski(u1_pre_topc(A_479),u1_pre_topc(A_34))
      | ~ v4_pre_topc(B_480,A_479)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ l1_pre_topc(A_479) ) ),
    inference(resolution,[status(thm)],[c_2915,c_1898])).

tff(c_1950,plain,(
    ! [A_302,B_31] :
      ( r2_hidden(k3_subset_1(u1_struct_0(A_302),B_31),u1_pre_topc(A_302))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_302),B_31),A_302)
      | ~ l1_pre_topc(A_302)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_302))) ) ),
    inference(resolution,[status(thm)],[c_34,c_1935])).

tff(c_2366,plain,(
    ! [D_389,A_390,B_391] :
      ( r2_hidden(D_389,k7_setfam_1(A_390,B_391))
      | ~ r2_hidden(k3_subset_1(A_390,D_389),B_391)
      | ~ m1_subset_1(D_389,k1_zfmisc_1(A_390))
      | ~ m1_subset_1(k7_setfam_1(A_390,B_391),k1_zfmisc_1(k1_zfmisc_1(A_390)))
      | ~ m1_subset_1(B_391,k1_zfmisc_1(k1_zfmisc_1(A_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7623,plain,(
    ! [B_1020,A_1021] :
      ( r2_hidden(B_1020,k7_setfam_1(u1_struct_0(A_1021),u1_pre_topc(A_1021)))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(A_1021),u1_pre_topc(A_1021)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1021))))
      | ~ m1_subset_1(u1_pre_topc(A_1021),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1021))))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1021),B_1020),A_1021)
      | ~ l1_pre_topc(A_1021)
      | ~ m1_subset_1(B_1020,k1_zfmisc_1(u1_struct_0(A_1021))) ) ),
    inference(resolution,[status(thm)],[c_1950,c_2366])).

tff(c_7628,plain,(
    ! [B_1022,A_1023] :
      ( r2_hidden(B_1022,k7_setfam_1(u1_struct_0(A_1023),u1_pre_topc(A_1023)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1023),B_1022),A_1023)
      | ~ l1_pre_topc(A_1023)
      | ~ m1_subset_1(B_1022,k1_zfmisc_1(u1_struct_0(A_1023)))
      | ~ m1_subset_1(u1_pre_topc(A_1023),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1023)))) ) ),
    inference(resolution,[status(thm)],[c_36,c_7623])).

tff(c_7632,plain,(
    ! [B_1024,A_1025] :
      ( r2_hidden(B_1024,k7_setfam_1(u1_struct_0(A_1025),u1_pre_topc(A_1025)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1025),B_1024),A_1025)
      | ~ m1_subset_1(B_1024,k1_zfmisc_1(u1_struct_0(A_1025)))
      | ~ l1_pre_topc(A_1025) ) ),
    inference(resolution,[status(thm)],[c_38,c_7628])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7738,plain,(
    ! [A_1065,A_1066] :
      ( r1_tarski(A_1065,k7_setfam_1(u1_struct_0(A_1066),u1_pre_topc(A_1066)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_1066),'#skF_2'(A_1065,k7_setfam_1(u1_struct_0(A_1066),u1_pre_topc(A_1066)))),A_1066)
      | ~ m1_subset_1('#skF_2'(A_1065,k7_setfam_1(u1_struct_0(A_1066),u1_pre_topc(A_1066))),k1_zfmisc_1(u1_struct_0(A_1066)))
      | ~ l1_pre_topc(A_1066) ) ),
    inference(resolution,[status(thm)],[c_7632,c_12])).

tff(c_7766,plain,(
    ! [A_1065,A_34] :
      ( r1_tarski(A_1065,k7_setfam_1(u1_struct_0(A_34),u1_pre_topc(A_34)))
      | ~ r1_tarski(u1_pre_topc(A_34),u1_pre_topc(A_34))
      | ~ v4_pre_topc('#skF_2'(A_1065,k7_setfam_1(u1_struct_0(A_34),u1_pre_topc(A_34))),A_34)
      | ~ m1_subset_1('#skF_2'(A_1065,k7_setfam_1(u1_struct_0(A_34),u1_pre_topc(A_34))),k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_2989,c_7738])).

tff(c_7790,plain,(
    ! [A_1067,A_1068] :
      ( r1_tarski(A_1067,k7_setfam_1(u1_struct_0(A_1068),u1_pre_topc(A_1068)))
      | ~ v4_pre_topc('#skF_2'(A_1067,k7_setfam_1(u1_struct_0(A_1068),u1_pre_topc(A_1068))),A_1068)
      | ~ m1_subset_1('#skF_2'(A_1067,k7_setfam_1(u1_struct_0(A_1068),u1_pre_topc(A_1068))),k1_zfmisc_1(u1_struct_0(A_1068)))
      | ~ l1_pre_topc(A_1068) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_7766])).

tff(c_7834,plain,(
    ! [A_1067] :
      ( r1_tarski(A_1067,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v4_pre_topc('#skF_2'(A_1067,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden('#skF_2'(A_1067,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1833,c_7790])).

tff(c_8003,plain,(
    ! [A_1075] :
      ( r1_tarski(A_1075,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v4_pre_topc('#skF_2'(A_1075,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_4')
      | ~ r2_hidden('#skF_2'(A_1075,k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7834])).

tff(c_8027,plain,
    ( r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ r2_hidden('#skF_2'('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_3225,c_8003])).

tff(c_8040,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_1825,c_8027])).

tff(c_8043,plain,
    ( ~ r1_tarski('#skF_5','#skF_5')
    | r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_69,c_8040])).

tff(c_8049,plain,(
    r1_tarski('#skF_5',k7_setfam_1(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_8043])).

tff(c_8051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1825,c_8049])).

%------------------------------------------------------------------------------
