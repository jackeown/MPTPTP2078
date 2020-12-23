%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1298+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:44 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 439 expanded)
%              Number of leaves         :   28 ( 158 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (1151 expanded)
%              Number of equality atoms :    6 (  65 expanded)
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

tff(f_108,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(c_50,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123,plain,(
    ! [A_75,B_76] :
      ( r2_hidden('#skF_2'(A_75,B_76),B_76)
      | v2_tops_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_128,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_132,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5')
    | v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_128])).

tff(c_133,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_132])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k7_setfam_1(A_32,B_33),k1_zfmisc_1(k1_zfmisc_1(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    ! [A_52,B_53] :
      ( k7_setfam_1(A_52,k7_setfam_1(A_52,B_53)) = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_71,plain,(
    k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_302,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,k7_setfam_1(u1_struct_0(A_111),B_112)),k7_setfam_1(u1_struct_0(A_111),B_112))
      | v2_tops_2(k7_setfam_1(u1_struct_0(A_111),B_112),A_111)
      | ~ l1_pre_topc(A_111)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111)))) ) ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_76,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k7_setfam_1(A_54,B_55),k1_zfmisc_1(k1_zfmisc_1(A_54)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    ! [A_42,C_44,B_43] :
      ( m1_subset_1(A_42,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_85,plain,(
    ! [A_42,A_54,B_55] :
      ( m1_subset_1(A_42,k1_zfmisc_1(A_54))
      | ~ r2_hidden(A_42,k7_setfam_1(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(resolution,[status(thm)],[c_76,c_44])).

tff(c_335,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1('#skF_2'(A_113,k7_setfam_1(u1_struct_0(A_113),B_114)),k1_zfmisc_1(u1_struct_0(A_113)))
      | v2_tops_2(k7_setfam_1(u1_struct_0(A_113),B_114),A_113)
      | ~ l1_pre_topc(A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113)))) ) ),
    inference(resolution,[status(thm)],[c_302,c_85])).

tff(c_344,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_335])).

tff(c_347,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_71,c_344])).

tff(c_348,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_347])).

tff(c_349,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_362,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_32,c_349])).

tff(c_366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_362])).

tff(c_367,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_368,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_56,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_434,plain,(
    ! [A_122,D_123,B_124] :
      ( r2_hidden(k3_subset_1(A_122,D_123),B_124)
      | ~ r2_hidden(D_123,k7_setfam_1(A_122,B_124))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(k7_setfam_1(A_122,B_124),k1_zfmisc_1(k1_zfmisc_1(A_122)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(A_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_442,plain,(
    ! [D_123] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_123),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_123,k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')))
      | ~ m1_subset_1(D_123,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_434])).

tff(c_449,plain,(
    ! [D_125] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_125),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ r2_hidden(D_125,'#skF_5')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_46,c_71,c_442])).

tff(c_460,plain,(
    ! [D_125] :
      ( m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_125),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ r2_hidden(D_125,'#skF_5')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_449,c_85])).

tff(c_471,plain,(
    ! [D_125] :
      ( m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_125),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_125,'#skF_5')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_460])).

tff(c_2,plain,(
    ! [C_10,A_1,B_7] :
      ( v3_pre_topc(C_10,A_1)
      | ~ r2_hidden(C_10,B_7)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3120,plain,(
    ! [D_298,A_299] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_298),A_299)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_298),k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),A_299)
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_299))))
      | ~ l1_pre_topc(A_299)
      | ~ r2_hidden(D_298,'#skF_5')
      | ~ m1_subset_1(D_298,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_449,c_2])).

tff(c_3128,plain,(
    ! [D_125] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_125),'#skF_4')
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_125,'#skF_5')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_471,c_3120])).

tff(c_3147,plain,(
    ! [D_300] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_300),'#skF_4')
      | ~ r2_hidden(D_300,'#skF_5')
      | ~ m1_subset_1(D_300,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_368,c_58,c_3128])).

tff(c_36,plain,(
    ! [B_38,A_36] :
      ( v4_pre_topc(B_38,A_36)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_36),B_38),A_36)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3150,plain,(
    ! [D_300] :
      ( v4_pre_topc(D_300,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_300,'#skF_5')
      | ~ m1_subset_1(D_300,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3147,c_36])).

tff(c_3154,plain,(
    ! [D_301] :
      ( v4_pre_topc(D_301,'#skF_4')
      | ~ r2_hidden(D_301,'#skF_5')
      | ~ m1_subset_1(D_301,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3150])).

tff(c_3172,plain,
    ( v4_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_367,c_3154])).

tff(c_3203,plain,(
    v4_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_3172])).

tff(c_12,plain,(
    ! [A_11,B_17] :
      ( ~ v4_pre_topc('#skF_2'(A_11,B_17),A_11)
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3219,plain,
    ( v2_tops_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3203,c_12])).

tff(c_3222,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3219])).

tff(c_3224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3222])).

tff(c_3225,plain,(
    ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3238,plain,(
    ! [A_308,B_309] :
      ( k7_setfam_1(A_308,k7_setfam_1(A_308,B_309)) = B_309
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k1_zfmisc_1(A_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3241,plain,(
    k7_setfam_1(u1_struct_0('#skF_4'),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_3238])).

tff(c_3414,plain,(
    ! [A_360,D_361,B_362] :
      ( r2_hidden(k3_subset_1(A_360,D_361),B_362)
      | ~ r2_hidden(D_361,k7_setfam_1(A_360,B_362))
      | ~ m1_subset_1(D_361,k1_zfmisc_1(A_360))
      | ~ m1_subset_1(k7_setfam_1(A_360,B_362),k1_zfmisc_1(k1_zfmisc_1(A_360)))
      | ~ m1_subset_1(B_362,k1_zfmisc_1(k1_zfmisc_1(A_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3424,plain,(
    ! [A_363,D_364,B_365] :
      ( r2_hidden(k3_subset_1(A_363,D_364),B_365)
      | ~ r2_hidden(D_364,k7_setfam_1(A_363,B_365))
      | ~ m1_subset_1(D_364,k1_zfmisc_1(A_363))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(k1_zfmisc_1(A_363))) ) ),
    inference(resolution,[status(thm)],[c_32,c_3414])).

tff(c_3454,plain,(
    ! [A_369,D_370,B_371] :
      ( r2_hidden(k3_subset_1(A_369,D_370),k7_setfam_1(A_369,B_371))
      | ~ r2_hidden(D_370,k7_setfam_1(A_369,k7_setfam_1(A_369,B_371)))
      | ~ m1_subset_1(D_370,k1_zfmisc_1(A_369))
      | ~ m1_subset_1(B_371,k1_zfmisc_1(k1_zfmisc_1(A_369))) ) ),
    inference(resolution,[status(thm)],[c_32,c_3424])).

tff(c_3246,plain,(
    ! [A_310,B_311] :
      ( m1_subset_1(k7_setfam_1(A_310,B_311),k1_zfmisc_1(k1_zfmisc_1(A_310)))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k1_zfmisc_1(A_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3255,plain,(
    ! [A_42,A_310,B_311] :
      ( m1_subset_1(A_42,k1_zfmisc_1(A_310))
      | ~ r2_hidden(A_42,k7_setfam_1(A_310,B_311))
      | ~ m1_subset_1(B_311,k1_zfmisc_1(k1_zfmisc_1(A_310))) ) ),
    inference(resolution,[status(thm)],[c_3246,c_44])).

tff(c_3474,plain,(
    ! [A_372,D_373,B_374] :
      ( m1_subset_1(k3_subset_1(A_372,D_373),k1_zfmisc_1(A_372))
      | ~ r2_hidden(D_373,k7_setfam_1(A_372,k7_setfam_1(A_372,B_374)))
      | ~ m1_subset_1(D_373,k1_zfmisc_1(A_372))
      | ~ m1_subset_1(B_374,k1_zfmisc_1(k1_zfmisc_1(A_372))) ) ),
    inference(resolution,[status(thm)],[c_3454,c_3255])).

tff(c_3491,plain,(
    ! [D_373] :
      ( m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_373),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_373,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_373,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3241,c_3474])).

tff(c_3548,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_3491])).

tff(c_3551,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_32,c_3548])).

tff(c_3555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3551])).

tff(c_3557,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_3491])).

tff(c_6,plain,(
    ! [A_1,B_7] :
      ( r2_hidden('#skF_1'(A_1,B_7),B_7)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3561,plain,
    ( r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3557,c_6])).

tff(c_3574,plain,
    ( r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
    | v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3561])).

tff(c_3575,plain,(
    r2_hidden('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3225,c_3574])).

tff(c_3592,plain,
    ( m1_subset_1('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_3575,c_3255])).

tff(c_3600,plain,(
    m1_subset_1('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3592])).

tff(c_3226,plain,(
    v2_tops_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3775,plain,(
    ! [D_392] :
      ( m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_392),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(D_392,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_3491])).

tff(c_3435,plain,(
    ! [D_366] :
      ( r2_hidden(k3_subset_1(u1_struct_0('#skF_4'),D_366),'#skF_5')
      | ~ r2_hidden(D_366,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_46,c_3424])).

tff(c_10,plain,(
    ! [C_20,A_11,B_17] :
      ( v4_pre_topc(C_20,A_11)
      | ~ r2_hidden(C_20,B_17)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3443,plain,(
    ! [D_366,A_11] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_366),A_11)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_4'),D_366),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ v2_tops_2('#skF_5',A_11)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11)
      | ~ r2_hidden(D_366,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3435,c_10])).

tff(c_3778,plain,(
    ! [D_392] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_392),'#skF_4')
      | ~ v2_tops_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_392,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3775,c_3443])).

tff(c_3811,plain,(
    ! [D_396] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_4'),D_396),'#skF_4')
      | ~ r2_hidden(D_396,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_396,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3226,c_3778])).

tff(c_40,plain,(
    ! [B_41,A_39] :
      ( v3_pre_topc(B_41,A_39)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_39),B_41),A_39)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3814,plain,(
    ! [D_396] :
      ( v3_pre_topc(D_396,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(D_396,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_396,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3811,c_40])).

tff(c_3818,plain,(
    ! [D_397] :
      ( v3_pre_topc(D_397,'#skF_4')
      | ~ r2_hidden(D_397,k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'))
      | ~ m1_subset_1(D_397,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3814])).

tff(c_3832,plain,
    ( v3_pre_topc('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3575,c_3818])).

tff(c_3846,plain,(
    v3_pre_topc('#skF_1'('#skF_4',k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3600,c_3832])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_pre_topc('#skF_1'(A_1,B_7),A_1)
      | v1_tops_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3854,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4')
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3846,c_4])).

tff(c_3857,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_4'),'#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3557,c_3854])).

tff(c_3859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3225,c_3857])).

%------------------------------------------------------------------------------
