%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1298+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:44 EST 2020

% Result     : Theorem 13.60s
% Output     : CNFRefutation 13.60s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 335 expanded)
%              Number of leaves         :   28 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 ( 917 expanded)
%              Number of equality atoms :    9 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > r2_hidden > m1_subset_1 > l1_pre_topc > k7_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v2_tops_2(B,A)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
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

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(c_48,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_55,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_177,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_2'(A_66,B_67),B_67)
      | v2_tops_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_185,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_177])).

tff(c_190,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_185])).

tff(c_191,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_190])).

tff(c_16,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_2'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k7_setfam_1(A_34,B_35),k1_zfmisc_1(k1_zfmisc_1(A_34)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    ! [A_48,B_49] :
      ( k7_setfam_1(A_48,k7_setfam_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_80,plain,(
    k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_73])).

tff(c_437,plain,(
    ! [A_94,D_95,B_96] :
      ( r2_hidden(k3_subset_1(A_94,D_95),B_96)
      | ~ r2_hidden(D_95,k7_setfam_1(A_94,B_96))
      | ~ m1_subset_1(D_95,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(k7_setfam_1(A_94,B_96),k1_zfmisc_1(k1_zfmisc_1(A_94)))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_447,plain,(
    ! [D_95] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_95),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_95,k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(D_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_437])).

tff(c_450,plain,(
    ! [D_95] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_95),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_95,'#skF_5')
      | ~ m1_subset_1(D_95,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80,c_447])).

tff(c_766,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_769,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_34,c_766])).

tff(c_773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_769])).

tff(c_775,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_54,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_54])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k3_subset_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_901,plain,(
    ! [D_122] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_122),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_122,'#skF_5')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_2,plain,(
    ! [C_10,A_1,B_7] :
      ( v3_pre_topc(C_10,A_1)
      | ~ r2_hidden(C_10,B_7)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15741,plain,(
    ! [D_470,A_471] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_470),A_471)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_470),k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),A_471)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_471))))
      | ~ l1_pre_topc(A_471)
      | ~ r2_hidden(D_470,'#skF_5')
      | ~ m1_subset_1(D_470,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_901,c_2])).

tff(c_15768,plain,(
    ! [B_33] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),B_33),'#skF_4')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(B_33,'#skF_5')
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_15741])).

tff(c_15778,plain,(
    ! [B_472] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),B_472),'#skF_4')
      | ~ r2_hidden(B_472,'#skF_5')
      | ~ m1_subset_1(B_472,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_775,c_56,c_15768])).

tff(c_246,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_2'(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | v2_tops_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74))))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    ! [A_36,B_37] :
      ( k3_subset_1(A_36,k3_subset_1(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_402,plain,(
    ! [A_91,B_92] :
      ( k3_subset_1(u1_struct_0(A_91),k3_subset_1(u1_struct_0(A_91),'#skF_2'(A_91,B_92))) = '#skF_2'(A_91,B_92)
      | v2_tops_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_91))))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_246,c_36])).

tff(c_42,plain,(
    ! [A_40,B_42] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_40),B_42),A_40)
      | ~ v3_pre_topc(B_42,A_40)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4408,plain,(
    ! [A_248,B_249] :
      ( v4_pre_topc('#skF_2'(A_248,B_249),A_248)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_248),'#skF_2'(A_248,B_249)),A_248)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(A_248),'#skF_2'(A_248,B_249)),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248)
      | v2_tops_2(B_249,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248))))
      | ~ l1_pre_topc(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_42])).

tff(c_4412,plain,(
    ! [A_248,B_249] :
      ( v4_pre_topc('#skF_2'(A_248,B_249),A_248)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_248),'#skF_2'(A_248,B_249)),A_248)
      | v2_tops_2(B_249,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_248))))
      | ~ l1_pre_topc(A_248)
      | ~ m1_subset_1('#skF_2'(A_248,B_249),k1_zfmisc_1(u1_struct_0(A_248))) ) ),
    inference(resolution,[status(thm)],[c_32,c_4408])).

tff(c_15786,plain,(
    ! [B_249] :
      ( v4_pre_topc('#skF_2'('#skF_4',B_249),'#skF_4')
      | v2_tops_2(B_249,'#skF_4')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_4',B_249),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_249),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_15778,c_4412])).

tff(c_16329,plain,(
    ! [B_483] :
      ( v4_pre_topc('#skF_2'('#skF_4',B_483),'#skF_4')
      | v2_tops_2(B_483,'#skF_4')
      | ~ m1_subset_1(B_483,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r2_hidden('#skF_2'('#skF_4',B_483),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_483),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_15786])).

tff(c_16333,plain,(
    ! [B_17] :
      ( v4_pre_topc('#skF_2'('#skF_4',B_17),'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_4',B_17),'#skF_5')
      | v2_tops_2(B_17,'#skF_4')
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_16329])).

tff(c_16337,plain,(
    ! [B_484] :
      ( v4_pre_topc('#skF_2'('#skF_4',B_484),'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_4',B_484),'#skF_5')
      | v2_tops_2(B_484,'#skF_4')
      | ~ m1_subset_1(B_484,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16333])).

tff(c_16393,plain,
    ( v4_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_16337])).

tff(c_16416,plain,
    ( v4_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_16393])).

tff(c_16417,plain,(
    v4_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_16416])).

tff(c_12,plain,(
    ! [A_11,B_17] :
      ( ~ v4_pre_topc('#skF_2'(A_11,B_17),A_11)
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16419,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16417,c_12])).

tff(c_16422,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_16419])).

tff(c_16424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_16422])).

tff(c_16425,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16445,plain,(
    ! [A_489,B_490] :
      ( k7_setfam_1(A_489,k7_setfam_1(A_489,B_490)) = B_490
      | ~ m1_subset_1(B_490,k1_zfmisc_1(k1_zfmisc_1(A_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16452,plain,(
    k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_16445])).

tff(c_16875,plain,(
    ! [A_538,D_539,B_540] :
      ( r2_hidden(k3_subset_1(A_538,D_539),B_540)
      | ~ r2_hidden(D_539,k7_setfam_1(A_538,B_540))
      | ~ m1_subset_1(D_539,k1_zfmisc_1(A_538))
      | ~ m1_subset_1(k7_setfam_1(A_538,B_540),k1_zfmisc_1(k1_zfmisc_1(A_538)))
      | ~ m1_subset_1(B_540,k1_zfmisc_1(k1_zfmisc_1(A_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16885,plain,(
    ! [D_539] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_539),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_539,k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(D_539,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16452,c_16875])).

tff(c_16888,plain,(
    ! [D_539] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_539),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_539,'#skF_5')
      | ~ m1_subset_1(D_539,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16452,c_16885])).

tff(c_17111,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_16888])).

tff(c_17129,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_34,c_17111])).

tff(c_17133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_17129])).

tff(c_17135,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_16888])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( r2_hidden('#skF_1'(A_1,B_7),B_7)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17143,plain,
    ( r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_17135,c_6])).

tff(c_17158,plain,
    ( r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_17143])).

tff(c_17159,plain,(
    r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_16425,c_17158])).

tff(c_16426,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_16889,plain,(
    ! [A_541,D_542,B_543] :
      ( r2_hidden(k3_subset_1(A_541,D_542),B_543)
      | ~ r2_hidden(D_542,k7_setfam_1(A_541,B_543))
      | ~ m1_subset_1(D_542,k1_zfmisc_1(A_541))
      | ~ m1_subset_1(B_543,k1_zfmisc_1(k1_zfmisc_1(A_541))) ) ),
    inference(resolution,[status(thm)],[c_34,c_16875])).

tff(c_16904,plain,(
    ! [D_544] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_544),'#skF_5')
      | ~ r2_hidden(D_544,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_544,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_16889])).

tff(c_10,plain,(
    ! [C_20,A_11,B_17] :
      ( v4_pre_topc(C_20,A_11)
      | ~ r2_hidden(C_20,B_17)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17778,plain,(
    ! [D_595,A_596] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_595),A_596)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_595),k1_zfmisc_1(u1_struct_0(A_596)))
      | ~ v2_tops_2('#skF_5',A_596)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_596))))
      | ~ l1_pre_topc(A_596)
      | ~ r2_hidden(D_595,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_595,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_16904,c_10])).

tff(c_17801,plain,(
    ! [B_33] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),B_33),'#skF_4')
      | ~ v2_tops_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(B_33,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_32,c_17778])).

tff(c_17809,plain,(
    ! [B_597] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),B_597),'#skF_4')
      | ~ r2_hidden(B_597,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_16426,c_17801])).

tff(c_40,plain,(
    ! [B_42,A_40] :
      ( v3_pre_topc(B_42,A_40)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_40),B_42),A_40)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_17812,plain,(
    ! [B_597] :
      ( v3_pre_topc(B_597,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(B_597,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(B_597,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_17809,c_40])).

tff(c_17839,plain,(
    ! [B_598] :
      ( v3_pre_topc(B_598,'#skF_4')
      | ~ r2_hidden(B_598,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(B_598,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_17812])).

tff(c_17869,plain,
    ( v3_pre_topc('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_17159,c_17839])).

tff(c_17880,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_17869])).

tff(c_17883,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_17880])).

tff(c_17886,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_17135,c_17883])).

tff(c_17888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16425,c_17886])).

tff(c_17889,plain,(
    v3_pre_topc('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_17869])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17892,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_17889,c_4])).

tff(c_17895,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_17135,c_17892])).

tff(c_17897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16425,c_17895])).

%------------------------------------------------------------------------------
