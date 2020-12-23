%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 704 expanded)
%              Number of leaves         :   27 ( 253 expanded)
%              Depth                    :   18
%              Number of atoms          :  188 (2483 expanded)
%              Number of equality atoms :   12 ( 402 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v1_tops_2(C,A) )
                     => v1_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_9)).

tff(f_61,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_32,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ~ v1_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_43,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [A_9,B_15] :
      ( m1_subset_1('#skF_1'(A_9,B_15),k1_zfmisc_1(u1_struct_0(A_9)))
      | v1_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_34] :
      ( m1_pre_topc(A_34,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ! [A_58,B_59] :
      ( m1_pre_topc(A_58,g1_pre_topc(u1_struct_0(B_59),u1_pre_topc(B_59)))
      | ~ m1_pre_topc(A_58,B_59)
      | ~ l1_pre_topc(B_59)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_67,plain,(
    ! [B_55,A_56] :
      ( m1_pre_topc(B_55,A_56)
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_67])).

tff(c_76,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_89,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,'#skF_2')
      | ~ m1_pre_topc(A_58,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_85,c_76])).

tff(c_98,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,'#skF_2')
      | ~ m1_pre_topc(A_58,'#skF_3')
      | ~ l1_pre_topc(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_95,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_58,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_85])).

tff(c_103,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_61,'#skF_2')
      | ~ l1_pre_topc(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_95])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( m1_pre_topc(B_5,A_3)
      | ~ m1_pre_topc(B_5,g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_61,'#skF_2')
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_103,c_8])).

tff(c_114,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,'#skF_3')
      | ~ m1_pre_topc(A_62,'#skF_2')
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_109])).

tff(c_121,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_125,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_121])).

tff(c_26,plain,(
    ! [B_37,A_35] :
      ( r1_tarski(u1_struct_0(B_37),u1_struct_0(A_35))
      | ~ m1_pre_topc(B_37,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(u1_struct_0(B_53),u1_struct_0(A_54))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [B_63,A_64] :
      ( u1_struct_0(B_63) = u1_struct_0(A_64)
      | ~ r1_tarski(u1_struct_0(A_64),u1_struct_0(B_63))
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_63,c_2])).

tff(c_137,plain,(
    ! [B_65,A_66] :
      ( u1_struct_0(B_65) = u1_struct_0(A_66)
      | ~ m1_pre_topc(A_66,B_65)
      | ~ l1_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_139,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_137])).

tff(c_150,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_139])).

tff(c_158,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_161,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_158])).

tff(c_164,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_161])).

tff(c_168,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_168])).

tff(c_173,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_30,plain,(
    v1_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_277,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | v1_tops_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_277])).

tff(c_286,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_281])).

tff(c_287,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_286])).

tff(c_552,plain,(
    ! [C_93,A_94,B_95] :
      ( v3_pre_topc(C_93,A_94)
      | ~ r2_hidden(C_93,B_95)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v1_tops_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_556,plain,(
    ! [A_96] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_96)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v1_tops_2('#skF_4',A_96)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_287,c_552])).

tff(c_563,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v1_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_556])).

tff(c_569,plain,
    ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_43,c_173,c_30,c_563])).

tff(c_570,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_573,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_570])).

tff(c_576,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_43,c_573])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_576])).

tff(c_580,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_174,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_579,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_22,plain,(
    ! [D_33,C_31,A_19] :
      ( v3_pre_topc(D_33,C_31)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(C_31)))
      | ~ v3_pre_topc(D_33,A_19)
      | ~ m1_pre_topc(C_31,A_19)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_593,plain,(
    ! [A_19] :
      ( v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_19)
      | ~ m1_pre_topc('#skF_3',A_19)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_580,c_22])).

tff(c_614,plain,(
    ! [A_100] :
      ( ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),A_100)
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_624,plain,
    ( ~ v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_614])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_580,c_174,c_579,c_624])).

tff(c_635,plain,(
    v3_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_16,plain,(
    ! [A_9,B_15] :
      ( ~ v3_pre_topc('#skF_1'(A_9,B_15),A_9)
      | v1_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_637,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_635,c_16])).

tff(c_640,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_43,c_637])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:17:15 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  
% 2.70/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.35  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.70/1.35  
% 2.70/1.35  %Foreground sorts:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Background operators:
% 2.70/1.35  
% 2.70/1.35  
% 2.70/1.35  %Foreground operators:
% 2.70/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.70/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.35  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.70/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.35  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.70/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.70/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.35  
% 2.93/1.37  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v1_tops_2(C, A)) => v1_tops_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_waybel_9)).
% 2.93/1.37  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.93/1.37  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.93/1.37  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.93/1.37  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.93/1.37  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 2.93/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.93/1.37  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 2.93/1.37  tff(c_32, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_28, plain, (~v1_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_44, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.93/1.37  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_43, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 2.93/1.37  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_20, plain, (![A_9, B_15]: (m1_subset_1('#skF_1'(A_9, B_15), k1_zfmisc_1(u1_struct_0(A_9))) | v1_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.37  tff(c_24, plain, (![A_34]: (m1_pre_topc(A_34, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.93/1.37  tff(c_85, plain, (![A_58, B_59]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0(B_59), u1_pre_topc(B_59))) | ~m1_pre_topc(A_58, B_59) | ~l1_pre_topc(B_59) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.93/1.37  tff(c_34, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_67, plain, (![B_55, A_56]: (m1_pre_topc(B_55, A_56) | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.37  tff(c_70, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_67])).
% 2.93/1.37  tff(c_76, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70])).
% 2.93/1.37  tff(c_89, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_85, c_76])).
% 2.93/1.37  tff(c_98, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_3') | ~l1_pre_topc(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_89])).
% 2.93/1.37  tff(c_95, plain, (![A_58]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_58, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_58))), inference(superposition, [status(thm), theory('equality')], [c_34, c_85])).
% 2.93/1.37  tff(c_103, plain, (![A_61]: (m1_pre_topc(A_61, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95])).
% 2.93/1.37  tff(c_8, plain, (![B_5, A_3]: (m1_pre_topc(B_5, A_3) | ~m1_pre_topc(B_5, g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.37  tff(c_109, plain, (![A_61]: (m1_pre_topc(A_61, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_103, c_8])).
% 2.93/1.37  tff(c_114, plain, (![A_62]: (m1_pre_topc(A_62, '#skF_3') | ~m1_pre_topc(A_62, '#skF_2') | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_109])).
% 2.93/1.37  tff(c_121, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.93/1.37  tff(c_125, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_121])).
% 2.93/1.37  tff(c_26, plain, (![B_37, A_35]: (r1_tarski(u1_struct_0(B_37), u1_struct_0(A_35)) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.37  tff(c_63, plain, (![B_53, A_54]: (r1_tarski(u1_struct_0(B_53), u1_struct_0(A_54)) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.93/1.37  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.37  tff(c_126, plain, (![B_63, A_64]: (u1_struct_0(B_63)=u1_struct_0(A_64) | ~r1_tarski(u1_struct_0(A_64), u1_struct_0(B_63)) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.93/1.37  tff(c_137, plain, (![B_65, A_66]: (u1_struct_0(B_65)=u1_struct_0(A_66) | ~m1_pre_topc(A_66, B_65) | ~l1_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_26, c_126])).
% 2.93/1.37  tff(c_139, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_125, c_137])).
% 2.93/1.37  tff(c_150, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_139])).
% 2.93/1.37  tff(c_158, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_150])).
% 2.93/1.37  tff(c_161, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_158])).
% 2.93/1.37  tff(c_164, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_161])).
% 2.93/1.37  tff(c_168, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_164])).
% 2.93/1.37  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_168])).
% 2.93/1.37  tff(c_173, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_150])).
% 2.93/1.37  tff(c_30, plain, (v1_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.93/1.37  tff(c_277, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | v1_tops_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.37  tff(c_281, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_43, c_277])).
% 2.93/1.37  tff(c_286, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_281])).
% 2.93/1.37  tff(c_287, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_286])).
% 2.93/1.37  tff(c_552, plain, (![C_93, A_94, B_95]: (v3_pre_topc(C_93, A_94) | ~r2_hidden(C_93, B_95) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~v1_tops_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94)))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.37  tff(c_556, plain, (![A_96]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_96) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_96))) | ~v1_tops_2('#skF_4', A_96) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_287, c_552])).
% 2.93/1.37  tff(c_563, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v1_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_556])).
% 2.93/1.37  tff(c_569, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_43, c_173, c_30, c_563])).
% 2.93/1.37  tff(c_570, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_569])).
% 2.93/1.37  tff(c_573, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_570])).
% 2.93/1.37  tff(c_576, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_43, c_573])).
% 2.93/1.37  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_576])).
% 2.93/1.37  tff(c_580, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_569])).
% 2.93/1.37  tff(c_174, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 2.93/1.37  tff(c_579, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_569])).
% 2.93/1.37  tff(c_22, plain, (![D_33, C_31, A_19]: (v3_pre_topc(D_33, C_31) | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(C_31))) | ~v3_pre_topc(D_33, A_19) | ~m1_pre_topc(C_31, A_19) | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.93/1.37  tff(c_593, plain, (![A_19]: (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_19) | ~m1_pre_topc('#skF_3', A_19) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_580, c_22])).
% 2.93/1.37  tff(c_614, plain, (![A_100]: (~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_100) | ~m1_pre_topc('#skF_3', A_100) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(splitLeft, [status(thm)], [c_593])).
% 2.93/1.37  tff(c_624, plain, (~v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_614])).
% 2.93/1.37  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_580, c_174, c_579, c_624])).
% 2.93/1.37  tff(c_635, plain, (v3_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_593])).
% 2.93/1.37  tff(c_16, plain, (![A_9, B_15]: (~v3_pre_topc('#skF_1'(A_9, B_15), A_9) | v1_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.93/1.37  tff(c_637, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_635, c_16])).
% 2.93/1.37  tff(c_640, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_43, c_637])).
% 2.93/1.37  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_640])).
% 2.93/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.37  
% 2.93/1.37  Inference rules
% 2.93/1.37  ----------------------
% 2.93/1.37  #Ref     : 0
% 2.93/1.37  #Sup     : 109
% 2.93/1.37  #Fact    : 0
% 2.93/1.37  #Define  : 0
% 2.93/1.37  #Split   : 4
% 2.93/1.37  #Chain   : 0
% 2.93/1.37  #Close   : 0
% 2.93/1.37  
% 2.93/1.37  Ordering : KBO
% 2.93/1.37  
% 2.93/1.37  Simplification rules
% 2.93/1.37  ----------------------
% 2.93/1.37  #Subsume      : 24
% 2.93/1.37  #Demod        : 160
% 2.93/1.37  #Tautology    : 43
% 2.93/1.37  #SimpNegUnit  : 6
% 2.93/1.37  #BackRed      : 3
% 2.93/1.37  
% 2.93/1.37  #Partial instantiations: 0
% 2.93/1.37  #Strategies tried      : 1
% 2.93/1.37  
% 2.93/1.37  Timing (in seconds)
% 2.93/1.37  ----------------------
% 2.93/1.38  Preprocessing        : 0.31
% 2.93/1.38  Parsing              : 0.17
% 2.93/1.38  CNF conversion       : 0.02
% 2.93/1.38  Main loop            : 0.31
% 2.93/1.38  Inferencing          : 0.11
% 2.93/1.38  Reduction            : 0.10
% 2.93/1.38  Demodulation         : 0.07
% 2.93/1.38  BG Simplification    : 0.02
% 2.93/1.38  Subsumption          : 0.07
% 2.93/1.38  Abstraction          : 0.01
% 2.93/1.38  MUC search           : 0.00
% 2.93/1.38  Cooper               : 0.00
% 2.93/1.38  Total                : 0.66
% 2.93/1.38  Index Insertion      : 0.00
% 2.93/1.38  Index Deletion       : 0.00
% 2.93/1.38  Index Matching       : 0.00
% 2.93/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
