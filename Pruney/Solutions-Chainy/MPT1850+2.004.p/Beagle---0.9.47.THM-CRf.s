%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:57 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 867 expanded)
%              Number of leaves         :   27 ( 304 expanded)
%              Depth                    :   19
%              Number of atoms          :  299 (2548 expanded)
%              Number of equality atoms :   19 ( 298 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v1_tdlat_3(A) )
             => v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tex_2)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_tdlat_3(A)
      <=> u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_105,axiom,(
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

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    ! [A_42] :
      ( k9_setfam_1(u1_struct_0(A_42)) = u1_pre_topc(A_42)
      | ~ v1_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ~ v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_26,plain,(
    ! [A_38] :
      ( m1_pre_topc(A_38,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_98,plain,(
    ! [A_58,B_59] :
      ( m1_pre_topc(A_58,g1_pre_topc(u1_struct_0(B_59),u1_pre_topc(B_59)))
      | ~ m1_pre_topc(A_58,B_59)
      | ~ l1_pre_topc(B_59)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_81,plain,(
    ! [B_55,A_56] :
      ( m1_pre_topc(B_55,A_56)
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_81])).

tff(c_90,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84])).

tff(c_102,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,'#skF_2')
      | ~ m1_pre_topc(A_58,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_98,c_90])).

tff(c_114,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,'#skF_2')
      | ~ m1_pre_topc(A_58,'#skF_1')
      | ~ l1_pre_topc(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_111,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_58,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_98])).

tff(c_126,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ m1_pre_topc(A_61,'#skF_2')
      | ~ l1_pre_topc(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_111])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( m1_pre_topc(B_9,A_7)
      | ~ m1_pre_topc(B_9,g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_61,'#skF_2')
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_141,plain,(
    ! [A_62] :
      ( m1_pre_topc(A_62,'#skF_1')
      | ~ m1_pre_topc(A_62,'#skF_2')
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_132])).

tff(c_148,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_141])).

tff(c_152,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_148])).

tff(c_28,plain,(
    ! [B_41,A_39] :
      ( r1_tarski(u1_struct_0(B_41),u1_struct_0(A_39))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_77,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(u1_struct_0(B_53),u1_struct_0(A_54))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [B_63,A_64] :
      ( u1_struct_0(B_63) = u1_struct_0(A_64)
      | ~ r1_tarski(u1_struct_0(A_64),u1_struct_0(B_63))
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_171,plain,(
    ! [B_65,A_66] :
      ( u1_struct_0(B_65) = u1_struct_0(A_66)
      | ~ m1_pre_topc(A_66,B_65)
      | ~ l1_pre_topc(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_173,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_152,c_171])).

tff(c_184,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_173])).

tff(c_192,plain,(
    ~ m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_201,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_192])).

tff(c_204,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_201])).

tff(c_207,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_204])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_207])).

tff(c_212,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_30,plain,(
    ! [A_42] :
      ( v1_tdlat_3(A_42)
      | k9_setfam_1(u1_struct_0(A_42)) != u1_pre_topc(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_265,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_30])).

tff(c_284,plain,
    ( v1_tdlat_3('#skF_2')
    | k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_265])).

tff(c_285,plain,(
    k9_setfam_1(u1_struct_0('#skF_1')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_284])).

tff(c_294,plain,
    ( u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_285])).

tff(c_296,plain,(
    u1_pre_topc('#skF_2') != u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_294])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_268,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_10])).

tff(c_287,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_268])).

tff(c_213,plain,(
    m1_pre_topc('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_411,plain,(
    ! [B_75,A_76] :
      ( v1_tops_2(B_75,A_76)
      | ~ r1_tarski(B_75,u1_pre_topc(A_76))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76))))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_417,plain,(
    ! [B_75] :
      ( v1_tops_2(B_75,'#skF_2')
      | ~ r1_tarski(B_75,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_411])).

tff(c_1583,plain,(
    ! [B_127] :
      ( v1_tops_2(B_127,'#skF_2')
      | ~ r1_tarski(B_127,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_417])).

tff(c_1590,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_287,c_1583])).

tff(c_1600,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1590])).

tff(c_297,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,u1_pre_topc(A_70))
      | ~ v1_tops_2(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_70))))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_300,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_287,c_297])).

tff(c_309,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_300])).

tff(c_326,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_1541,plain,(
    ! [D_123,C_124,A_125] :
      ( v1_tops_2(D_123,C_124)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_124))))
      | ~ v1_tops_2(D_123,A_125)
      | ~ m1_pre_topc(C_124,A_125)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1543,plain,(
    ! [A_125] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_1')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_125)
      | ~ m1_pre_topc('#skF_1',A_125)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_287,c_1541])).

tff(c_2773,plain,(
    ! [A_170] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_170)
      | ~ m1_pre_topc('#skF_1',A_170)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170))))
      | ~ l1_pre_topc(A_170) ) ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_1543])).

tff(c_2801,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2773])).

tff(c_2825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_287,c_213,c_1600,c_2801])).

tff(c_2826,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_2829,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_1')
    | ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2826,c_2])).

tff(c_2832,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_2829])).

tff(c_303,plain,(
    ! [B_69] :
      ( r1_tarski(B_69,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_69,'#skF_2')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_297])).

tff(c_3031,plain,(
    ! [B_184] :
      ( r1_tarski(B_184,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_184,'#skF_2')
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_303])).

tff(c_3042,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_3031])).

tff(c_3050,plain,
    ( r1_tarski(u1_pre_topc('#skF_1'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3042])).

tff(c_3051,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2832,c_3050])).

tff(c_2952,plain,(
    ! [C_178,A_179,B_180] :
      ( m1_subset_1(C_178,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_179))))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_180))))
      | ~ m1_pre_topc(B_180,A_179)
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3088,plain,(
    ! [A_189,A_190] :
      ( m1_subset_1(u1_pre_topc(A_189),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190))))
      | ~ m1_pre_topc(A_189,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ l1_pre_topc(A_189) ) ),
    inference(resolution,[status(thm)],[c_10,c_2952])).

tff(c_3109,plain,(
    ! [A_189] :
      ( m1_subset_1(u1_pre_topc(A_189),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_189,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_3088])).

tff(c_3122,plain,(
    ! [A_191] :
      ( m1_subset_1(u1_pre_topc(A_191),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_191,'#skF_2')
      | ~ l1_pre_topc(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3109])).

tff(c_22,plain,(
    ! [B_37,A_35] :
      ( v1_tops_2(B_37,A_35)
      | ~ r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3135,plain,(
    ! [A_191] :
      ( v1_tops_2(u1_pre_topc(A_191),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_191),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_191,'#skF_2')
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_3122,c_22])).

tff(c_3263,plain,(
    ! [A_198] :
      ( v1_tops_2(u1_pre_topc(A_198),'#skF_1')
      | ~ r1_tarski(u1_pre_topc(A_198),u1_pre_topc('#skF_1'))
      | ~ m1_pre_topc(A_198,'#skF_2')
      | ~ l1_pre_topc(A_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3135])).

tff(c_3273,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3263])).

tff(c_3280,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_213,c_3273])).

tff(c_18,plain,(
    ! [C_19,A_13,B_17] :
      ( m1_subset_1(C_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_17))))
      | ~ m1_pre_topc(B_17,A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3466,plain,(
    ! [A_208,A_209,A_210] :
      ( m1_subset_1(u1_pre_topc(A_208),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_209))))
      | ~ m1_pre_topc(A_210,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ m1_pre_topc(A_208,A_210)
      | ~ l1_pre_topc(A_210)
      | ~ l1_pre_topc(A_208) ) ),
    inference(resolution,[status(thm)],[c_3088,c_18])).

tff(c_3478,plain,(
    ! [A_208,A_58] :
      ( m1_subset_1(u1_pre_topc(A_208),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_208,A_58)
      | ~ l1_pre_topc(A_208)
      | ~ m1_pre_topc(A_58,'#skF_1')
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_114,c_3466])).

tff(c_3558,plain,(
    ! [A_213,A_214] :
      ( m1_subset_1(u1_pre_topc(A_213),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_213,A_214)
      | ~ l1_pre_topc(A_213)
      | ~ m1_pre_topc(A_214,'#skF_1')
      | ~ l1_pre_topc(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_212,c_3478])).

tff(c_3564,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_3558])).

tff(c_3581,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_152,c_42,c_3564])).

tff(c_3810,plain,(
    ! [C_222,A_223] :
      ( m1_subset_1(C_222,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_223))))
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc('#skF_2',A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2952])).

tff(c_3834,plain,(
    ! [A_223] :
      ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_223))))
      | ~ m1_pre_topc('#skF_2',A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_3581,c_3810])).

tff(c_20,plain,(
    ! [D_34,C_32,A_20] :
      ( v1_tops_2(D_34,C_32)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_32))))
      | ~ v1_tops_2(D_34,A_20)
      | ~ m1_pre_topc(C_32,A_20)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20))))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3727,plain,(
    ! [A_218,A_219,A_220] :
      ( v1_tops_2(u1_pre_topc(A_218),A_219)
      | ~ v1_tops_2(u1_pre_topc(A_218),A_220)
      | ~ m1_pre_topc(A_219,A_220)
      | ~ m1_subset_1(u1_pre_topc(A_218),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_220))))
      | ~ l1_pre_topc(A_220)
      | ~ m1_pre_topc(A_218,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_3088,c_20])).

tff(c_3735,plain,(
    ! [A_218] :
      ( v1_tops_2(u1_pre_topc(A_218),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_218),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_218),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1')
      | ~ m1_pre_topc(A_218,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_218) ) ),
    inference(resolution,[status(thm)],[c_152,c_3727])).

tff(c_6193,plain,(
    ! [A_290] :
      ( v1_tops_2(u1_pre_topc(A_290),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc(A_290),'#skF_1')
      | ~ m1_subset_1(u1_pre_topc(A_290),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(A_290,'#skF_2')
      | ~ l1_pre_topc(A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_3735])).

tff(c_6224,plain,
    ( v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2')
    | ~ v1_tops_2(u1_pre_topc('#skF_1'),'#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_3834,c_6193])).

tff(c_6274,plain,(
    v1_tops_2(u1_pre_topc('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_152,c_213,c_3280,c_6224])).

tff(c_6276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3051,c_6274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.13  
% 5.89/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.14  %$ v1_tops_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_tdlat_3 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.89/2.14  
% 5.89/2.14  %Foreground sorts:
% 5.89/2.14  
% 5.89/2.14  
% 5.89/2.14  %Background operators:
% 5.89/2.14  
% 5.89/2.14  
% 5.89/2.14  %Foreground operators:
% 5.89/2.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.89/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.89/2.14  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 5.89/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.89/2.14  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.89/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.14  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 5.89/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.89/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.89/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.89/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.89/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.89/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.89/2.14  
% 6.01/2.17  tff(f_123, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v1_tdlat_3(A)) => v1_tdlat_3(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tex_2)).
% 6.01/2.17  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (v1_tdlat_3(A) <=> (u1_pre_topc(A) = k9_setfam_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tdlat_3)).
% 6.01/2.17  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.01/2.17  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.01/2.17  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.01/2.17  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 6.01/2.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.01/2.17  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.01/2.17  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 6.01/2.17  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 6.01/2.17  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 6.01/2.17  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.17  tff(c_36, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.17  tff(c_32, plain, (![A_42]: (k9_setfam_1(u1_struct_0(A_42))=u1_pre_topc(A_42) | ~v1_tdlat_3(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.17  tff(c_34, plain, (~v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.17  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.17  tff(c_26, plain, (![A_38]: (m1_pre_topc(A_38, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.01/2.17  tff(c_98, plain, (![A_58, B_59]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0(B_59), u1_pre_topc(B_59))) | ~m1_pre_topc(A_58, B_59) | ~l1_pre_topc(B_59) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.01/2.17  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.01/2.17  tff(c_81, plain, (![B_55, A_56]: (m1_pre_topc(B_55, A_56) | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.01/2.17  tff(c_84, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_81])).
% 6.01/2.17  tff(c_90, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84])).
% 6.01/2.17  tff(c_102, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_98, c_90])).
% 6.01/2.17  tff(c_114, plain, (![A_58]: (m1_pre_topc(A_58, '#skF_2') | ~m1_pre_topc(A_58, '#skF_1') | ~l1_pre_topc(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 6.01/2.17  tff(c_111, plain, (![A_58]: (m1_pre_topc(A_58, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_58, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_58))), inference(superposition, [status(thm), theory('equality')], [c_38, c_98])).
% 6.01/2.17  tff(c_126, plain, (![A_61]: (m1_pre_topc(A_61, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_111])).
% 6.01/2.17  tff(c_12, plain, (![B_9, A_7]: (m1_pre_topc(B_9, A_7) | ~m1_pre_topc(B_9, g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.01/2.17  tff(c_132, plain, (![A_61]: (m1_pre_topc(A_61, '#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_126, c_12])).
% 6.01/2.17  tff(c_141, plain, (![A_62]: (m1_pre_topc(A_62, '#skF_1') | ~m1_pre_topc(A_62, '#skF_2') | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_132])).
% 6.01/2.17  tff(c_148, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_141])).
% 6.01/2.17  tff(c_152, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_148])).
% 6.01/2.17  tff(c_28, plain, (![B_41, A_39]: (r1_tarski(u1_struct_0(B_41), u1_struct_0(A_39)) | ~m1_pre_topc(B_41, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.01/2.17  tff(c_77, plain, (![B_53, A_54]: (r1_tarski(u1_struct_0(B_53), u1_struct_0(A_54)) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.01/2.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.01/2.17  tff(c_160, plain, (![B_63, A_64]: (u1_struct_0(B_63)=u1_struct_0(A_64) | ~r1_tarski(u1_struct_0(A_64), u1_struct_0(B_63)) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64))), inference(resolution, [status(thm)], [c_77, c_2])).
% 6.01/2.17  tff(c_171, plain, (![B_65, A_66]: (u1_struct_0(B_65)=u1_struct_0(A_66) | ~m1_pre_topc(A_66, B_65) | ~l1_pre_topc(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_28, c_160])).
% 6.01/2.17  tff(c_173, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_152, c_171])).
% 6.01/2.17  tff(c_184, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_173])).
% 6.01/2.17  tff(c_192, plain, (~m1_pre_topc('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_184])).
% 6.01/2.17  tff(c_201, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_114, c_192])).
% 6.01/2.17  tff(c_204, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_201])).
% 6.01/2.17  tff(c_207, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_204])).
% 6.01/2.17  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_207])).
% 6.01/2.17  tff(c_212, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 6.01/2.17  tff(c_30, plain, (![A_42]: (v1_tdlat_3(A_42) | k9_setfam_1(u1_struct_0(A_42))!=u1_pre_topc(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.01/2.17  tff(c_265, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_212, c_30])).
% 6.01/2.17  tff(c_284, plain, (v1_tdlat_3('#skF_2') | k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_265])).
% 6.01/2.17  tff(c_285, plain, (k9_setfam_1(u1_struct_0('#skF_1'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_284])).
% 6.01/2.17  tff(c_294, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_285])).
% 6.01/2.17  tff(c_296, plain, (u1_pre_topc('#skF_2')!=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_294])).
% 6.01/2.17  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.01/2.17  tff(c_268, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_212, c_10])).
% 6.01/2.17  tff(c_287, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_268])).
% 6.01/2.17  tff(c_213, plain, (m1_pre_topc('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_184])).
% 6.01/2.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.01/2.17  tff(c_411, plain, (![B_75, A_76]: (v1_tops_2(B_75, A_76) | ~r1_tarski(B_75, u1_pre_topc(A_76)) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_76)))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.17  tff(c_417, plain, (![B_75]: (v1_tops_2(B_75, '#skF_2') | ~r1_tarski(B_75, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_411])).
% 6.01/2.17  tff(c_1583, plain, (![B_127]: (v1_tops_2(B_127, '#skF_2') | ~r1_tarski(B_127, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_417])).
% 6.01/2.17  tff(c_1590, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_287, c_1583])).
% 6.01/2.17  tff(c_1600, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1590])).
% 6.01/2.17  tff(c_297, plain, (![B_69, A_70]: (r1_tarski(B_69, u1_pre_topc(A_70)) | ~v1_tops_2(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_70)))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.17  tff(c_300, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_287, c_297])).
% 6.01/2.17  tff(c_309, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_300])).
% 6.01/2.17  tff(c_326, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_309])).
% 6.01/2.17  tff(c_1541, plain, (![D_123, C_124, A_125]: (v1_tops_2(D_123, C_124) | ~m1_subset_1(D_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_124)))) | ~v1_tops_2(D_123, A_125) | ~m1_pre_topc(C_124, A_125) | ~m1_subset_1(D_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.01/2.17  tff(c_1543, plain, (![A_125]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_1') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_125) | ~m1_pre_topc('#skF_1', A_125) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125))), inference(resolution, [status(thm)], [c_287, c_1541])).
% 6.01/2.17  tff(c_2773, plain, (![A_170]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_170) | ~m1_pre_topc('#skF_1', A_170) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_170)))) | ~l1_pre_topc(A_170))), inference(negUnitSimplification, [status(thm)], [c_326, c_1543])).
% 6.01/2.17  tff(c_2801, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_212, c_2773])).
% 6.01/2.17  tff(c_2825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_287, c_213, c_1600, c_2801])).
% 6.01/2.17  tff(c_2826, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_309])).
% 6.01/2.17  tff(c_2829, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_1') | ~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2826, c_2])).
% 6.01/2.17  tff(c_2832, plain, (~r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_296, c_2829])).
% 6.01/2.17  tff(c_303, plain, (![B_69]: (r1_tarski(B_69, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_69, '#skF_2') | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_297])).
% 6.01/2.17  tff(c_3031, plain, (![B_184]: (r1_tarski(B_184, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_184, '#skF_2') | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_303])).
% 6.01/2.17  tff(c_3042, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_3031])).
% 6.01/2.17  tff(c_3050, plain, (r1_tarski(u1_pre_topc('#skF_1'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3042])).
% 6.01/2.17  tff(c_3051, plain, (~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2832, c_3050])).
% 6.01/2.17  tff(c_2952, plain, (![C_178, A_179, B_180]: (m1_subset_1(C_178, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_179)))) | ~m1_subset_1(C_178, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_180)))) | ~m1_pre_topc(B_180, A_179) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.01/2.17  tff(c_3088, plain, (![A_189, A_190]: (m1_subset_1(u1_pre_topc(A_189), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_190)))) | ~m1_pre_topc(A_189, A_190) | ~l1_pre_topc(A_190) | ~l1_pre_topc(A_189))), inference(resolution, [status(thm)], [c_10, c_2952])).
% 6.01/2.17  tff(c_3109, plain, (![A_189]: (m1_subset_1(u1_pre_topc(A_189), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_189, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_189))), inference(superposition, [status(thm), theory('equality')], [c_212, c_3088])).
% 6.01/2.17  tff(c_3122, plain, (![A_191]: (m1_subset_1(u1_pre_topc(A_191), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_191, '#skF_2') | ~l1_pre_topc(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3109])).
% 6.01/2.17  tff(c_22, plain, (![B_37, A_35]: (v1_tops_2(B_37, A_35) | ~r1_tarski(B_37, u1_pre_topc(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.01/2.17  tff(c_3135, plain, (![A_191]: (v1_tops_2(u1_pre_topc(A_191), '#skF_1') | ~r1_tarski(u1_pre_topc(A_191), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_191, '#skF_2') | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_3122, c_22])).
% 6.01/2.17  tff(c_3263, plain, (![A_198]: (v1_tops_2(u1_pre_topc(A_198), '#skF_1') | ~r1_tarski(u1_pre_topc(A_198), u1_pre_topc('#skF_1')) | ~m1_pre_topc(A_198, '#skF_2') | ~l1_pre_topc(A_198))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3135])).
% 6.01/2.17  tff(c_3273, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_3263])).
% 6.01/2.17  tff(c_3280, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_213, c_3273])).
% 6.01/2.17  tff(c_18, plain, (![C_19, A_13, B_17]: (m1_subset_1(C_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~m1_subset_1(C_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_17)))) | ~m1_pre_topc(B_17, A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.01/2.17  tff(c_3466, plain, (![A_208, A_209, A_210]: (m1_subset_1(u1_pre_topc(A_208), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_209)))) | ~m1_pre_topc(A_210, A_209) | ~l1_pre_topc(A_209) | ~m1_pre_topc(A_208, A_210) | ~l1_pre_topc(A_210) | ~l1_pre_topc(A_208))), inference(resolution, [status(thm)], [c_3088, c_18])).
% 6.01/2.17  tff(c_3478, plain, (![A_208, A_58]: (m1_subset_1(u1_pre_topc(A_208), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(A_208, A_58) | ~l1_pre_topc(A_208) | ~m1_pre_topc(A_58, '#skF_1') | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_114, c_3466])).
% 6.01/2.17  tff(c_3558, plain, (![A_213, A_214]: (m1_subset_1(u1_pre_topc(A_213), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_213, A_214) | ~l1_pre_topc(A_213) | ~m1_pre_topc(A_214, '#skF_1') | ~l1_pre_topc(A_214))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_212, c_3478])).
% 6.01/2.17  tff(c_3564, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_213, c_3558])).
% 6.01/2.17  tff(c_3581, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_152, c_42, c_3564])).
% 6.01/2.17  tff(c_3810, plain, (![C_222, A_223]: (m1_subset_1(C_222, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_223)))) | ~m1_subset_1(C_222, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc('#skF_2', A_223) | ~l1_pre_topc(A_223))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2952])).
% 6.01/2.17  tff(c_3834, plain, (![A_223]: (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_223)))) | ~m1_pre_topc('#skF_2', A_223) | ~l1_pre_topc(A_223))), inference(resolution, [status(thm)], [c_3581, c_3810])).
% 6.01/2.17  tff(c_20, plain, (![D_34, C_32, A_20]: (v1_tops_2(D_34, C_32) | ~m1_subset_1(D_34, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_32)))) | ~v1_tops_2(D_34, A_20) | ~m1_pre_topc(C_32, A_20) | ~m1_subset_1(D_34, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_20)))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.01/2.17  tff(c_3727, plain, (![A_218, A_219, A_220]: (v1_tops_2(u1_pre_topc(A_218), A_219) | ~v1_tops_2(u1_pre_topc(A_218), A_220) | ~m1_pre_topc(A_219, A_220) | ~m1_subset_1(u1_pre_topc(A_218), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_220)))) | ~l1_pre_topc(A_220) | ~m1_pre_topc(A_218, A_219) | ~l1_pre_topc(A_219) | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_3088, c_20])).
% 6.01/2.17  tff(c_3735, plain, (![A_218]: (v1_tops_2(u1_pre_topc(A_218), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_218), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_218), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1') | ~m1_pre_topc(A_218, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_218))), inference(resolution, [status(thm)], [c_152, c_3727])).
% 6.01/2.17  tff(c_6193, plain, (![A_290]: (v1_tops_2(u1_pre_topc(A_290), '#skF_2') | ~v1_tops_2(u1_pre_topc(A_290), '#skF_1') | ~m1_subset_1(u1_pre_topc(A_290), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_pre_topc(A_290, '#skF_2') | ~l1_pre_topc(A_290))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_3735])).
% 6.01/2.17  tff(c_6224, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_1'), '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_3834, c_6193])).
% 6.01/2.17  tff(c_6274, plain, (v1_tops_2(u1_pre_topc('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_152, c_213, c_3280, c_6224])).
% 6.01/2.17  tff(c_6276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3051, c_6274])).
% 6.01/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.17  
% 6.01/2.17  Inference rules
% 6.01/2.17  ----------------------
% 6.01/2.17  #Ref     : 0
% 6.01/2.17  #Sup     : 1122
% 6.01/2.17  #Fact    : 0
% 6.01/2.17  #Define  : 0
% 6.01/2.17  #Split   : 6
% 6.01/2.17  #Chain   : 0
% 6.01/2.17  #Close   : 0
% 6.01/2.17  
% 6.01/2.17  Ordering : KBO
% 6.01/2.17  
% 6.01/2.17  Simplification rules
% 6.01/2.17  ----------------------
% 6.01/2.17  #Subsume      : 259
% 6.01/2.17  #Demod        : 1791
% 6.01/2.17  #Tautology    : 455
% 6.01/2.17  #SimpNegUnit  : 72
% 6.01/2.17  #BackRed      : 1
% 6.01/2.17  
% 6.01/2.17  #Partial instantiations: 0
% 6.01/2.17  #Strategies tried      : 1
% 6.01/2.17  
% 6.01/2.17  Timing (in seconds)
% 6.01/2.17  ----------------------
% 6.01/2.17  Preprocessing        : 0.32
% 6.01/2.17  Parsing              : 0.17
% 6.01/2.17  CNF conversion       : 0.02
% 6.01/2.17  Main loop            : 1.05
% 6.01/2.17  Inferencing          : 0.35
% 6.01/2.17  Reduction            : 0.34
% 6.01/2.17  Demodulation         : 0.23
% 6.01/2.17  BG Simplification    : 0.04
% 6.01/2.17  Subsumption          : 0.26
% 6.01/2.17  Abstraction          : 0.05
% 6.01/2.17  MUC search           : 0.00
% 6.01/2.17  Cooper               : 0.00
% 6.01/2.17  Total                : 1.42
% 6.01/2.17  Index Insertion      : 0.00
% 6.01/2.17  Index Deletion       : 0.00
% 6.01/2.17  Index Matching       : 0.00
% 6.01/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
