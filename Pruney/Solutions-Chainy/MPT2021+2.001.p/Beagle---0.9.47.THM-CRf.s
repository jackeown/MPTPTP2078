%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:11 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
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
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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
                        & v2_tops_2(C,A) )
                     => v2_tops_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_waybel_9)).

tff(f_61,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_32,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ~ v2_tops_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ~ v2_tops_2('#skF_4','#skF_3') ),
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
      | v2_tops_2(B_15,A_9)
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
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_277,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),B_72)
      | v2_tops_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71))))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v2_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_43,c_277])).

tff(c_286,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_281])).

tff(c_287,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_286])).

tff(c_552,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_pre_topc(C_93,A_94)
      | ~ r2_hidden(C_93,B_95)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v2_tops_2(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_556,plain,(
    ! [A_96] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_96)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v2_tops_2('#skF_4',A_96)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_287,c_552])).

tff(c_563,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_tops_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_556])).

tff(c_569,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_43,c_173,c_30,c_563])).

tff(c_570,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_573,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_570])).

tff(c_576,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
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
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_22,plain,(
    ! [D_33,C_31,A_19] :
      ( v4_pre_topc(D_33,C_31)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(C_31)))
      | ~ v4_pre_topc(D_33,A_19)
      | ~ m1_pre_topc(C_31,A_19)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_593,plain,(
    ! [A_19] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_19)
      | ~ m1_pre_topc('#skF_3',A_19)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(resolution,[status(thm)],[c_580,c_22])).

tff(c_614,plain,(
    ! [A_100] :
      ( ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),A_100)
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(splitLeft,[status(thm)],[c_593])).

tff(c_624,plain,
    ( ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_614])).

tff(c_634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_580,c_174,c_579,c_624])).

tff(c_635,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_593])).

tff(c_16,plain,(
    ! [A_9,B_15] :
      ( ~ v4_pre_topc('#skF_1'(A_9,B_15),A_9)
      | v2_tops_2(B_15,A_9)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9))))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_637,plain,
    ( v2_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_635,c_16])).

tff(c_640,plain,(
    v2_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_43,c_637])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.37  
% 2.78/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.37  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.78/1.37  
% 2.78/1.37  %Foreground sorts:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Background operators:
% 2.78/1.37  
% 2.78/1.37  
% 2.78/1.37  %Foreground operators:
% 2.78/1.37  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.37  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.78/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.78/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.37  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.78/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.37  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.78/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.37  
% 2.78/1.39  tff(f_109, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tops_2(C, A)) => v2_tops_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_waybel_9)).
% 2.78/1.39  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 2.78/1.39  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.78/1.39  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 2.78/1.39  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 2.78/1.39  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 2.78/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.39  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 2.78/1.39  tff(c_32, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_28, plain, (~v2_tops_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_44, plain, (~v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28])).
% 2.78/1.39  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_43, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 2.78/1.39  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_20, plain, (![A_9, B_15]: (m1_subset_1('#skF_1'(A_9, B_15), k1_zfmisc_1(u1_struct_0(A_9))) | v2_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.39  tff(c_24, plain, (![A_34]: (m1_pre_topc(A_34, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.39  tff(c_85, plain, (![A_58, B_59]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0(B_59), u1_pre_topc(B_59))) | ~m1_pre_topc(A_58, B_59) | ~l1_pre_topc(B_59) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.78/1.39  tff(c_34, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_67, plain, (![B_55, A_56]: (m1_pre_topc(B_55, A_56) | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.39  tff(c_70, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_67])).
% 2.78/1.39  tff(c_76, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70])).
% 2.78/1.39  tff(c_89, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_85, c_76])).
% 2.78/1.39  tff(c_98, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_3') | ~l1_pre_topc(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_89])).
% 2.78/1.39  tff(c_95, plain, (![A_58]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_58, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_58))), inference(superposition, [status(thm), theory('equality')], [c_34, c_85])).
% 2.78/1.39  tff(c_103, plain, (![A_61]: (m1_pre_topc(A_61, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_95])).
% 2.78/1.39  tff(c_8, plain, (![B_5, A_3]: (m1_pre_topc(B_5, A_3) | ~m1_pre_topc(B_5, g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.78/1.39  tff(c_109, plain, (![A_61]: (m1_pre_topc(A_61, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_103, c_8])).
% 2.78/1.39  tff(c_114, plain, (![A_62]: (m1_pre_topc(A_62, '#skF_3') | ~m1_pre_topc(A_62, '#skF_2') | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_109])).
% 2.78/1.39  tff(c_121, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.78/1.39  tff(c_125, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_121])).
% 2.78/1.39  tff(c_26, plain, (![B_37, A_35]: (r1_tarski(u1_struct_0(B_37), u1_struct_0(A_35)) | ~m1_pre_topc(B_37, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.78/1.39  tff(c_63, plain, (![B_53, A_54]: (r1_tarski(u1_struct_0(B_53), u1_struct_0(A_54)) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.78/1.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.39  tff(c_126, plain, (![B_63, A_64]: (u1_struct_0(B_63)=u1_struct_0(A_64) | ~r1_tarski(u1_struct_0(A_64), u1_struct_0(B_63)) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_63, c_2])).
% 2.78/1.39  tff(c_137, plain, (![B_65, A_66]: (u1_struct_0(B_65)=u1_struct_0(A_66) | ~m1_pre_topc(A_66, B_65) | ~l1_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_26, c_126])).
% 2.78/1.39  tff(c_139, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_125, c_137])).
% 2.78/1.39  tff(c_150, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_139])).
% 2.78/1.39  tff(c_158, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_150])).
% 2.78/1.39  tff(c_161, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_158])).
% 2.78/1.39  tff(c_164, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_161])).
% 2.78/1.39  tff(c_168, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_164])).
% 2.78/1.39  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_168])).
% 2.78/1.39  tff(c_173, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_150])).
% 2.78/1.39  tff(c_30, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.78/1.39  tff(c_277, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), B_72) | v2_tops_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_71)))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.39  tff(c_281, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v2_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_43, c_277])).
% 2.78/1.39  tff(c_286, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_281])).
% 2.78/1.39  tff(c_287, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_286])).
% 2.78/1.39  tff(c_552, plain, (![C_93, A_94, B_95]: (v4_pre_topc(C_93, A_94) | ~r2_hidden(C_93, B_95) | ~m1_subset_1(C_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~v2_tops_2(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94)))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.39  tff(c_556, plain, (![A_96]: (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_96) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_96))) | ~v2_tops_2('#skF_4', A_96) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_287, c_552])).
% 2.78/1.39  tff(c_563, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_556])).
% 2.78/1.39  tff(c_569, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_43, c_173, c_30, c_563])).
% 2.78/1.39  tff(c_570, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_569])).
% 2.78/1.39  tff(c_573, plain, (v2_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_570])).
% 2.78/1.39  tff(c_576, plain, (v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_43, c_573])).
% 2.78/1.39  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_576])).
% 2.78/1.39  tff(c_580, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_569])).
% 2.78/1.39  tff(c_174, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_150])).
% 2.78/1.39  tff(c_579, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_569])).
% 2.78/1.39  tff(c_22, plain, (![D_33, C_31, A_19]: (v4_pre_topc(D_33, C_31) | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(C_31))) | ~v4_pre_topc(D_33, A_19) | ~m1_pre_topc(C_31, A_19) | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.39  tff(c_593, plain, (![A_19]: (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_19) | ~m1_pre_topc('#skF_3', A_19) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(resolution, [status(thm)], [c_580, c_22])).
% 2.78/1.39  tff(c_614, plain, (![A_100]: (~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_100) | ~m1_pre_topc('#skF_3', A_100) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100))), inference(splitLeft, [status(thm)], [c_593])).
% 2.78/1.39  tff(c_624, plain, (~v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_614])).
% 2.78/1.39  tff(c_634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_580, c_174, c_579, c_624])).
% 2.78/1.39  tff(c_635, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_593])).
% 2.78/1.39  tff(c_16, plain, (![A_9, B_15]: (~v4_pre_topc('#skF_1'(A_9, B_15), A_9) | v2_tops_2(B_15, A_9) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_9)))) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.39  tff(c_637, plain, (v2_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_635, c_16])).
% 2.78/1.39  tff(c_640, plain, (v2_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_43, c_637])).
% 2.78/1.39  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_640])).
% 2.78/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  Inference rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Ref     : 0
% 2.78/1.39  #Sup     : 109
% 2.78/1.39  #Fact    : 0
% 2.78/1.39  #Define  : 0
% 2.78/1.39  #Split   : 4
% 2.78/1.39  #Chain   : 0
% 2.78/1.39  #Close   : 0
% 2.78/1.39  
% 2.78/1.39  Ordering : KBO
% 2.78/1.39  
% 2.78/1.39  Simplification rules
% 2.78/1.39  ----------------------
% 2.78/1.39  #Subsume      : 24
% 2.78/1.39  #Demod        : 160
% 2.78/1.39  #Tautology    : 43
% 2.78/1.39  #SimpNegUnit  : 6
% 2.78/1.39  #BackRed      : 3
% 2.78/1.39  
% 2.78/1.39  #Partial instantiations: 0
% 2.78/1.39  #Strategies tried      : 1
% 2.78/1.39  
% 2.78/1.39  Timing (in seconds)
% 2.78/1.39  ----------------------
% 2.78/1.40  Preprocessing        : 0.29
% 2.78/1.40  Parsing              : 0.15
% 2.78/1.40  CNF conversion       : 0.02
% 2.78/1.40  Main loop            : 0.32
% 2.78/1.40  Inferencing          : 0.11
% 2.78/1.40  Reduction            : 0.10
% 2.78/1.40  Demodulation         : 0.07
% 2.78/1.40  BG Simplification    : 0.02
% 2.78/1.40  Subsumption          : 0.07
% 2.78/1.40  Abstraction          : 0.02
% 2.78/1.40  MUC search           : 0.00
% 2.78/1.40  Cooper               : 0.00
% 2.78/1.40  Total                : 0.65
% 2.78/1.40  Index Insertion      : 0.00
% 2.78/1.40  Index Deletion       : 0.00
% 2.78/1.40  Index Matching       : 0.00
% 2.78/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
