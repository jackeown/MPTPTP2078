%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 146 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  165 ( 433 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(c_44,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_420,plain,(
    ! [A_83,B_84] :
      ( '#skF_1'(A_83,B_84) != B_84
      | v3_tex_2(B_84,A_83)
      | ~ v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_427,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_420])).

tff(c_435,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_427])).

tff(c_436,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_435])).

tff(c_625,plain,(
    ! [A_101,B_102] :
      ( v2_tex_2('#skF_1'(A_101,B_102),A_101)
      | v3_tex_2(B_102,A_101)
      | ~ v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_630,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_625])).

tff(c_637,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_630])).

tff(c_638,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_637])).

tff(c_509,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,'#skF_1'(A_92,B_91))
      | v3_tex_2(B_91,A_92)
      | ~ v2_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_514,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_509])).

tff(c_521,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_514])).

tff(c_522,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_521])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_757,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1('#skF_1'(A_112,B_113),k1_zfmisc_1(u1_struct_0(A_112)))
      | v3_tex_2(B_113,A_112)
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1035,plain,(
    ! [A_131,B_132] :
      ( r1_tarski('#skF_1'(A_131,B_132),u1_struct_0(A_131))
      | v3_tex_2(B_132,A_131)
      | ~ v2_tex_2(B_132,A_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_757,c_16])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1171,plain,(
    ! [A_141,B_142] :
      ( k4_xboole_0('#skF_1'(A_141,B_142),u1_struct_0(A_141)) = k1_xboole_0
      | v3_tex_2(B_142,A_141)
      | ~ v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141) ) ),
    inference(resolution,[status(thm)],[c_1035,c_4])).

tff(c_1180,plain,
    ( k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1171])).

tff(c_1189,plain,
    ( k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_1180])).

tff(c_1190,plain,(
    k4_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1189])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1220,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = k4_xboole_0('#skF_1'('#skF_3','#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_8])).

tff(c_1240,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1220])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_54,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_209,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_218,plain,(
    ! [A_7,B_57] : k9_subset_1(A_7,B_57,A_7) = k3_xboole_0(B_57,A_7) ),
    inference(resolution,[status(thm)],[c_57,c_209])).

tff(c_48,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_382,plain,(
    ! [A_78,B_79] :
      ( k2_pre_topc(A_78,B_79) = u1_struct_0(A_78)
      | ~ v1_tops_1(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_389,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_382])).

tff(c_397,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_389])).

tff(c_1263,plain,(
    ! [A_145,B_146,C_147] :
      ( k9_subset_1(u1_struct_0(A_145),B_146,k2_pre_topc(A_145,C_147)) = C_147
      | ~ r1_tarski(C_147,B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v2_tex_2(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1272,plain,(
    ! [B_146] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_146,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_146)
      | ~ v2_tex_2(B_146,'#skF_3')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1263])).

tff(c_1281,plain,(
    ! [B_146] :
      ( k3_xboole_0(B_146,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_146)
      | ~ v2_tex_2(B_146,'#skF_3')
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_218,c_397,c_1272])).

tff(c_1285,plain,(
    ! [B_148] :
      ( k3_xboole_0(B_148,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_148)
      | ~ v2_tex_2(B_148,'#skF_3')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1281])).

tff(c_1351,plain,(
    ! [A_150] :
      ( k3_xboole_0(A_150,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_150)
      | ~ v2_tex_2(A_150,'#skF_3')
      | ~ r1_tarski(A_150,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_1285])).

tff(c_1398,plain,(
    ! [A_151] :
      ( k3_xboole_0(A_151,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_151)
      | ~ v2_tex_2(A_151,'#skF_3')
      | k4_xboole_0(A_151,u1_struct_0('#skF_3')) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_1351])).

tff(c_1401,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_1398])).

tff(c_1415,plain,(
    '#skF_1'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_522,c_1240,c_1401])).

tff(c_1417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_1415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.59  
% 3.52/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.59  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.52/1.59  
% 3.52/1.59  %Foreground sorts:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Background operators:
% 3.52/1.59  
% 3.52/1.59  
% 3.52/1.59  %Foreground operators:
% 3.52/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.52/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.59  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.52/1.59  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.52/1.59  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.52/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.52/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.52/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.52/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.52/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.52/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.52/1.59  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.52/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.59  
% 3.77/1.61  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tex_2)).
% 3.77/1.61  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.77/1.61  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.77/1.61  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.77/1.61  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.77/1.61  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.77/1.61  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.77/1.61  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.77/1.61  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.77/1.61  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 3.77/1.61  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 3.77/1.61  tff(c_44, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_46, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_420, plain, (![A_83, B_84]: ('#skF_1'(A_83, B_84)!=B_84 | v3_tex_2(B_84, A_83) | ~v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.61  tff(c_427, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_420])).
% 3.77/1.61  tff(c_435, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_427])).
% 3.77/1.61  tff(c_436, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_44, c_435])).
% 3.77/1.61  tff(c_625, plain, (![A_101, B_102]: (v2_tex_2('#skF_1'(A_101, B_102), A_101) | v3_tex_2(B_102, A_101) | ~v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.61  tff(c_630, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_625])).
% 3.77/1.61  tff(c_637, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_630])).
% 3.77/1.61  tff(c_638, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_637])).
% 3.77/1.61  tff(c_509, plain, (![B_91, A_92]: (r1_tarski(B_91, '#skF_1'(A_92, B_91)) | v3_tex_2(B_91, A_92) | ~v2_tex_2(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.61  tff(c_514, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_509])).
% 3.77/1.61  tff(c_521, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_514])).
% 3.77/1.61  tff(c_522, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_521])).
% 3.77/1.61  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.61  tff(c_757, plain, (![A_112, B_113]: (m1_subset_1('#skF_1'(A_112, B_113), k1_zfmisc_1(u1_struct_0(A_112))) | v3_tex_2(B_113, A_112) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.77/1.61  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/1.61  tff(c_1035, plain, (![A_131, B_132]: (r1_tarski('#skF_1'(A_131, B_132), u1_struct_0(A_131)) | v3_tex_2(B_132, A_131) | ~v2_tex_2(B_132, A_131) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_757, c_16])).
% 3.77/1.61  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.61  tff(c_1171, plain, (![A_141, B_142]: (k4_xboole_0('#skF_1'(A_141, B_142), u1_struct_0(A_141))=k1_xboole_0 | v3_tex_2(B_142, A_141) | ~v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141))), inference(resolution, [status(thm)], [c_1035, c_4])).
% 3.77/1.61  tff(c_1180, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0 | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1171])).
% 3.77/1.61  tff(c_1189, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0 | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_1180])).
% 3.77/1.61  tff(c_1190, plain, (k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_1189])).
% 3.77/1.61  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.77/1.61  tff(c_1220, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))=k4_xboole_0('#skF_1'('#skF_3', '#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1190, c_8])).
% 3.77/1.61  tff(c_1240, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1220])).
% 3.77/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.77/1.61  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.77/1.61  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_54, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_10, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.77/1.61  tff(c_12, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.77/1.61  tff(c_57, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 3.77/1.61  tff(c_209, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.77/1.61  tff(c_218, plain, (![A_7, B_57]: (k9_subset_1(A_7, B_57, A_7)=k3_xboole_0(B_57, A_7))), inference(resolution, [status(thm)], [c_57, c_209])).
% 3.77/1.61  tff(c_48, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.77/1.61  tff(c_382, plain, (![A_78, B_79]: (k2_pre_topc(A_78, B_79)=u1_struct_0(A_78) | ~v1_tops_1(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.77/1.61  tff(c_389, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_382])).
% 3.77/1.61  tff(c_397, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_389])).
% 3.77/1.61  tff(c_1263, plain, (![A_145, B_146, C_147]: (k9_subset_1(u1_struct_0(A_145), B_146, k2_pre_topc(A_145, C_147))=C_147 | ~r1_tarski(C_147, B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_145))) | ~v2_tex_2(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.77/1.61  tff(c_1272, plain, (![B_146]: (k9_subset_1(u1_struct_0('#skF_3'), B_146, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_146) | ~v2_tex_2(B_146, '#skF_3') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_1263])).
% 3.77/1.61  tff(c_1281, plain, (![B_146]: (k3_xboole_0(B_146, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_146) | ~v2_tex_2(B_146, '#skF_3') | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_218, c_397, c_1272])).
% 3.77/1.61  tff(c_1285, plain, (![B_148]: (k3_xboole_0(B_148, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_148) | ~v2_tex_2(B_148, '#skF_3') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_1281])).
% 3.77/1.61  tff(c_1351, plain, (![A_150]: (k3_xboole_0(A_150, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', A_150) | ~v2_tex_2(A_150, '#skF_3') | ~r1_tarski(A_150, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_1285])).
% 3.77/1.61  tff(c_1398, plain, (![A_151]: (k3_xboole_0(A_151, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', A_151) | ~v2_tex_2(A_151, '#skF_3') | k4_xboole_0(A_151, u1_struct_0('#skF_3'))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1351])).
% 3.77/1.61  tff(c_1401, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1190, c_1398])).
% 3.77/1.61  tff(c_1415, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_638, c_522, c_1240, c_1401])).
% 3.77/1.61  tff(c_1417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_1415])).
% 3.77/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.61  
% 3.77/1.61  Inference rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Ref     : 0
% 3.77/1.61  #Sup     : 305
% 3.77/1.61  #Fact    : 0
% 3.77/1.61  #Define  : 0
% 3.77/1.61  #Split   : 5
% 3.77/1.61  #Chain   : 0
% 3.77/1.61  #Close   : 0
% 3.77/1.61  
% 3.77/1.61  Ordering : KBO
% 3.77/1.61  
% 3.77/1.61  Simplification rules
% 3.77/1.61  ----------------------
% 3.77/1.61  #Subsume      : 23
% 3.77/1.61  #Demod        : 263
% 3.77/1.61  #Tautology    : 122
% 3.77/1.61  #SimpNegUnit  : 19
% 3.77/1.61  #BackRed      : 0
% 3.77/1.61  
% 3.77/1.61  #Partial instantiations: 0
% 3.77/1.61  #Strategies tried      : 1
% 3.77/1.61  
% 3.77/1.61  Timing (in seconds)
% 3.77/1.61  ----------------------
% 3.77/1.61  Preprocessing        : 0.30
% 3.77/1.61  Parsing              : 0.16
% 3.77/1.61  CNF conversion       : 0.02
% 3.77/1.61  Main loop            : 0.50
% 3.77/1.61  Inferencing          : 0.18
% 3.77/1.61  Reduction            : 0.17
% 3.77/1.61  Demodulation         : 0.12
% 3.77/1.61  BG Simplification    : 0.02
% 3.77/1.61  Subsumption          : 0.10
% 3.77/1.61  Abstraction          : 0.03
% 3.77/1.61  MUC search           : 0.00
% 3.77/1.61  Cooper               : 0.00
% 3.77/1.61  Total                : 0.83
% 3.77/1.61  Index Insertion      : 0.00
% 3.77/1.61  Index Deletion       : 0.00
% 3.77/1.61  Index Matching       : 0.00
% 3.77/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
