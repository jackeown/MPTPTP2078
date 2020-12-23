%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:24 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :  269 (1361 expanded)
%              Number of leaves         :   38 ( 466 expanded)
%              Depth                    :   23
%              Number of atoms          :  541 (5094 expanded)
%              Number of equality atoms :   85 ( 373 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_tops_1,type,(
    v6_tops_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v4_tops_1,type,(
    v4_tops_1: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v3_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v6_tops_1(D,B) )
                      & ( v6_tops_1(C,A)
                       => ( v3_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v6_tops_1(B,A)
          <=> B = k1_tops_1(A,k2_pre_topc(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,k1_tops_1(A,B)) = k2_pre_topc(A,k1_tops_1(A,k2_pre_topc(A,k1_tops_1(A,B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_14359,plain,(
    ! [A_546,B_547] :
      ( m1_subset_1(k2_pre_topc(A_546,B_547),k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14380,plain,(
    ! [A_546,B_547] :
      ( r1_tarski(k2_pre_topc(A_546,B_547),u1_struct_0(A_546))
      | ~ m1_subset_1(B_547,k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ l1_pre_topc(A_546) ) ),
    inference(resolution,[status(thm)],[c_14359,c_14])).

tff(c_66,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_13832,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_68,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    ~ v6_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_332,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k2_pre_topc(A_81,B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_346,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k2_pre_topc(A_81,B_82),u1_struct_0(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_332,c_14])).

tff(c_111,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_77,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_1030,plain,(
    ! [A_120,B_121] :
      ( k1_tops_1(A_120,k2_pre_topc(A_120,B_121)) = B_121
      | ~ v6_tops_1(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1041,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1030])).

tff(c_1050,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_77,c_1041])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_802,plain,(
    ! [A_108,B_109] :
      ( v3_pre_topc(k1_tops_1(A_108,B_109),A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_816,plain,(
    ! [A_108,A_9] :
      ( v3_pre_topc(k1_tops_1(A_108,A_9),A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | ~ r1_tarski(A_9,u1_struct_0(A_108)) ) ),
    inference(resolution,[status(thm)],[c_16,c_802])).

tff(c_1054,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_816])).

tff(c_1064,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1054])).

tff(c_1065,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_1064])).

tff(c_1073,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_346,c_1065])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1073])).

tff(c_1079,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1081,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_64])).

tff(c_1082,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1081])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1249,plain,(
    ! [B_134,A_135] :
      ( r1_tarski(B_134,k2_pre_topc(A_135,B_134))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1256,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1249])).

tff(c_1263,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1256])).

tff(c_1084,plain,(
    ! [A_124,B_125] :
      ( k3_subset_1(A_124,k3_subset_1(A_124,B_125)) = B_125
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1093,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_1084])).

tff(c_1098,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(A_126,B_127) = k3_subset_1(A_126,B_127)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1110,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1098])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1135,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1110,c_8])).

tff(c_2004,plain,(
    ! [B_175,A_176] :
      ( v4_pre_topc(B_175,A_176)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_176),B_175),A_176)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2015,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_2004])).

tff(c_2020,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1079,c_2015])).

tff(c_2143,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2020])).

tff(c_2146,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_2143])).

tff(c_2150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1135,c_2146])).

tff(c_2151,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2020])).

tff(c_2152,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2020])).

tff(c_24,plain,(
    ! [A_16,B_18] :
      ( k2_pre_topc(A_16,B_18) = B_18
      | ~ v4_pre_topc(B_18,A_16)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2157,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2152,c_24])).

tff(c_2175,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2151,c_2157])).

tff(c_3425,plain,(
    ! [A_221,B_222] :
      ( k3_subset_1(u1_struct_0(A_221),k2_pre_topc(A_221,k3_subset_1(u1_struct_0(A_221),B_222))) = k1_tops_1(A_221,B_222)
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3452,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2175,c_3425])).

tff(c_3472,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_1093,c_3452])).

tff(c_2207,plain,(
    ! [A_181,B_182] :
      ( k1_tops_1(A_181,k2_pre_topc(A_181,B_182)) = B_182
      | ~ v6_tops_1(B_182,A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2220,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_2207])).

tff(c_2232,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_77,c_2220])).

tff(c_4199,plain,(
    ! [B_229,A_230] :
      ( v4_tops_1(B_229,A_230)
      | ~ r1_tarski(B_229,k2_pre_topc(A_230,k1_tops_1(A_230,B_229)))
      | ~ r1_tarski(k1_tops_1(A_230,k2_pre_topc(A_230,B_229)),B_229)
      | ~ m1_subset_1(B_229,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4224,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2232,c_4199])).

tff(c_4243,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_6,c_1263,c_3472,c_4224])).

tff(c_4245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_4243])).

tff(c_4246,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_32,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k1_tops_1(A_22,k2_pre_topc(A_22,B_24)),B_24)
      | ~ v4_tops_1(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4331,plain,(
    ! [B_239,A_240] :
      ( r1_tarski(B_239,k2_pre_topc(A_240,B_239))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4336,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_4331])).

tff(c_4342,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4336])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k2_pre_topc(A_11,B_12),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k1_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4250,plain,(
    ! [A_231,B_232] :
      ( k3_subset_1(A_231,k3_subset_1(A_231,B_232)) = B_232
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4258,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_4250])).

tff(c_4318,plain,(
    ! [A_237,B_238] :
      ( k4_xboole_0(A_237,B_238) = k3_subset_1(A_237,B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_237)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4329,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4318])).

tff(c_4358,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4329,c_8])).

tff(c_4247,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1081])).

tff(c_1078,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4249,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4247,c_1078])).

tff(c_5100,plain,(
    ! [B_283,A_284] :
      ( v4_pre_topc(B_283,A_284)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_284),B_283),A_284)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5114,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4258,c_5100])).

tff(c_5118,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4249,c_5114])).

tff(c_5271,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5118])).

tff(c_5274,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_5271])).

tff(c_5278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4358,c_5274])).

tff(c_5279,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5118])).

tff(c_5280,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5118])).

tff(c_5285,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_5280,c_24])).

tff(c_5303,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5279,c_5285])).

tff(c_6418,plain,(
    ! [A_322,B_323] :
      ( k3_subset_1(u1_struct_0(A_322),k2_pre_topc(A_322,k3_subset_1(u1_struct_0(A_322),B_323))) = k1_tops_1(A_322,B_323)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6445,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5303,c_6418])).

tff(c_6468,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_4258,c_6445])).

tff(c_6673,plain,(
    ! [A_324,B_325] :
      ( k2_pre_topc(A_324,k1_tops_1(A_324,k2_pre_topc(A_324,k1_tops_1(A_324,B_325)))) = k2_pre_topc(A_324,k1_tops_1(A_324,B_325))
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_6714,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6468,c_6673])).

tff(c_6740,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_6468,c_6714])).

tff(c_4441,plain,(
    ! [A_245,B_246] :
      ( m1_subset_1(k2_pre_topc(A_245,B_246),k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4455,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(k2_pre_topc(A_245,B_246),u1_struct_0(A_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(resolution,[status(thm)],[c_4441,c_14])).

tff(c_6835,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6740,c_4455])).

tff(c_6858,plain,
    ( r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6835])).

tff(c_8523,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6858])).

tff(c_8526,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_8523])).

tff(c_8532,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_8526])).

tff(c_8572,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_8532])).

tff(c_8579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_8572])).

tff(c_8580,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6858])).

tff(c_6903,plain,(
    ! [A_326,B_327,C_328] :
      ( r1_tarski(k1_tops_1(A_326,B_327),k1_tops_1(A_326,C_328))
      | ~ r1_tarski(B_327,C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_326)))
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_6917,plain,(
    ! [C_328] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_328))
      | ~ r1_tarski('#skF_4',C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6468,c_6903])).

tff(c_7069,plain,(
    ! [C_330] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_330))
      | ~ r1_tarski('#skF_4',C_330)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_6917])).

tff(c_7095,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_9))
      | ~ r1_tarski('#skF_4',A_9)
      | ~ r1_tarski(A_9,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_7069])).

tff(c_8583,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8580,c_7095])).

tff(c_8601,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4342,c_8583])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8623,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8601,c_2])).

tff(c_8968,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8623])).

tff(c_9015,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_8968])).

tff(c_9022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_4246,c_9015])).

tff(c_9023,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8623])).

tff(c_34,plain,(
    ! [B_27,A_25] :
      ( v6_tops_1(B_27,A_25)
      | k1_tops_1(A_25,k2_pre_topc(A_25,B_27)) != B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9074,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9023,c_34])).

tff(c_9112,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_9074])).

tff(c_9114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_9112])).

tff(c_9116,plain,(
    ~ v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_70,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v6_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_9117,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_9118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9116,c_9117])).

tff(c_9119,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_9357,plain,(
    ! [B_384,A_385] :
      ( r1_tarski(B_384,k2_pre_topc(A_385,B_384))
      | ~ m1_subset_1(B_384,k1_zfmisc_1(u1_struct_0(A_385)))
      | ~ l1_pre_topc(A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_9362,plain,
    ( r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_9357])).

tff(c_9368,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9362])).

tff(c_9156,plain,(
    ! [A_371,B_372] :
      ( k4_xboole_0(A_371,B_372) = k3_subset_1(A_371,B_372)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(A_371)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9167,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_4') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_9156])).

tff(c_9175,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9167,c_8])).

tff(c_9240,plain,(
    ! [A_376,B_377] :
      ( k3_subset_1(A_376,k3_subset_1(A_376,B_377)) = B_377
      | ~ m1_subset_1(B_377,k1_zfmisc_1(A_376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9248,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_9240])).

tff(c_11650,plain,(
    ! [A_481,B_482] :
      ( k3_subset_1(u1_struct_0(A_481),k2_pre_topc(A_481,k3_subset_1(u1_struct_0(A_481),B_482))) = k1_tops_1(A_481,B_482)
      | ~ m1_subset_1(B_482,k1_zfmisc_1(u1_struct_0(A_481)))
      | ~ l1_pre_topc(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11688,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9248,c_11650])).

tff(c_11696,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11688])).

tff(c_11993,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_11696])).

tff(c_11996,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_11993])).

tff(c_12000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9175,c_11996])).

tff(c_12001,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11696])).

tff(c_9585,plain,(
    ! [A_394,B_395] :
      ( m1_subset_1(k2_pre_topc(A_394,B_395),k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ m1_subset_1(B_395,k1_zfmisc_1(u1_struct_0(A_394)))
      | ~ l1_pre_topc(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_subset_1(A_7,k3_subset_1(A_7,B_8)) = B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12963,plain,(
    ! [A_495,B_496] :
      ( k3_subset_1(u1_struct_0(A_495),k3_subset_1(u1_struct_0(A_495),k2_pre_topc(A_495,B_496))) = k2_pre_topc(A_495,B_496)
      | ~ m1_subset_1(B_496,k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ l1_pre_topc(A_495) ) ),
    inference(resolution,[status(thm)],[c_9585,c_12])).

tff(c_12993,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k2_pre_topc('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12001,c_12963])).

tff(c_13024,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))) = k2_pre_topc('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_12993])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k3_subset_1(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13375,plain,(
    ! [A_504,B_505] :
      ( k4_xboole_0(u1_struct_0(A_504),k2_pre_topc(A_504,B_505)) = k3_subset_1(u1_struct_0(A_504),k2_pre_topc(A_504,B_505))
      | ~ m1_subset_1(B_505,k1_zfmisc_1(u1_struct_0(A_504)))
      | ~ l1_pre_topc(A_504) ) ),
    inference(resolution,[status(thm)],[c_9585,c_10])).

tff(c_13392,plain,
    ( k4_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_13375])).

tff(c_13412,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2','#skF_4')) = k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12001,c_13392])).

tff(c_9197,plain,(
    ! [B_373,A_374] :
      ( k4_xboole_0(B_373,A_374) = k3_subset_1(B_373,A_374)
      | ~ r1_tarski(A_374,B_373) ) ),
    inference(resolution,[status(thm)],[c_16,c_9156])).

tff(c_9321,plain,(
    ! [A_382,B_383] : k4_xboole_0(A_382,k4_xboole_0(A_382,B_383)) = k3_subset_1(A_382,k4_xboole_0(A_382,B_383)) ),
    inference(resolution,[status(thm)],[c_8,c_9197])).

tff(c_9333,plain,(
    ! [A_382,B_383] : r1_tarski(k3_subset_1(A_382,k4_xboole_0(A_382,B_383)),A_382) ),
    inference(superposition,[status(thm),theory(equality)],[c_9321,c_8])).

tff(c_13440,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),k1_tops_1('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'))),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13412,c_9333])).

tff(c_13460,plain,(
    r1_tarski(k2_pre_topc('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13024,c_13440])).

tff(c_9727,plain,(
    ! [A_404,B_405] :
      ( k2_pre_topc(A_404,B_405) = B_405
      | ~ v4_pre_topc(B_405,A_404)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ l1_pre_topc(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_9751,plain,(
    ! [A_406,A_407] :
      ( k2_pre_topc(A_406,A_407) = A_407
      | ~ v4_pre_topc(A_407,A_406)
      | ~ l1_pre_topc(A_406)
      | ~ r1_tarski(A_407,u1_struct_0(A_406)) ) ),
    inference(resolution,[status(thm)],[c_16,c_9727])).

tff(c_9785,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9175,c_9751])).

tff(c_9812,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9785])).

tff(c_10402,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9812])).

tff(c_9115,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_10710,plain,(
    ! [B_450,A_451] :
      ( v4_pre_topc(B_450,A_451)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_451),B_450),A_451)
      | ~ m1_subset_1(B_450,k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ l1_pre_topc(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_10727,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9248,c_10710])).

tff(c_10733,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_9115,c_10727])).

tff(c_10734,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10402,c_10733])).

tff(c_10737,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_10734])).

tff(c_10741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9175,c_10737])).

tff(c_10742,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_9812])).

tff(c_11674,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10742,c_11650])).

tff(c_11692,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_9248,c_11674])).

tff(c_12084,plain,(
    ! [A_485,B_486,C_487] :
      ( r1_tarski(k1_tops_1(A_485,B_486),k1_tops_1(A_485,C_487))
      | ~ r1_tarski(B_486,C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ m1_subset_1(B_486,k1_zfmisc_1(u1_struct_0(A_485)))
      | ~ l1_pre_topc(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_12092,plain,(
    ! [C_487] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_487))
      | ~ r1_tarski('#skF_4',C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11692,c_12084])).

tff(c_13226,plain,(
    ! [C_502] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',C_502))
      | ~ r1_tarski('#skF_4',C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_12092])).

tff(c_13252,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_2',A_9))
      | ~ r1_tarski('#skF_4',A_9)
      | ~ r1_tarski(A_9,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_16,c_13226])).

tff(c_13465,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')))
    | ~ r1_tarski('#skF_4',k2_pre_topc('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_13460,c_13252])).

tff(c_13483,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9368,c_13465])).

tff(c_13541,plain,
    ( k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4'
    | ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_13483,c_2])).

tff(c_13714,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13541])).

tff(c_13720,plain,
    ( ~ v4_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_13714])).

tff(c_13727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_9119,c_13720])).

tff(c_13728,plain,(
    k1_tops_1('#skF_2',k2_pre_topc('#skF_2','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13541])).

tff(c_13773,plain,
    ( v6_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13728,c_34])).

tff(c_13811,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_13773])).

tff(c_13813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13811])).

tff(c_13814,plain,(
    v6_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_14715,plain,(
    ! [A_568,B_569] :
      ( k1_tops_1(A_568,k2_pre_topc(A_568,B_569)) = B_569
      | ~ v6_tops_1(B_569,A_568)
      | ~ m1_subset_1(B_569,k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ l1_pre_topc(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14726,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_14715])).

tff(c_14735,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13814,c_14726])).

tff(c_14090,plain,(
    ! [A_532,B_533] :
      ( v3_pre_topc(k1_tops_1(A_532,B_533),A_532)
      | ~ m1_subset_1(B_533,k1_zfmisc_1(u1_struct_0(A_532)))
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14098,plain,(
    ! [A_532,A_9] :
      ( v3_pre_topc(k1_tops_1(A_532,A_9),A_532)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | ~ r1_tarski(A_9,u1_struct_0(A_532)) ) ),
    inference(resolution,[status(thm)],[c_16,c_14090])).

tff(c_14761,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14735,c_14098])).

tff(c_14770,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_14761])).

tff(c_14771,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1','#skF_3'),u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_13832,c_14770])).

tff(c_14777,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14380,c_14771])).

tff(c_14781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_14777])).

tff(c_14783,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_13815,plain,(
    v6_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ v6_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_14785,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13815,c_62])).

tff(c_14786,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_14785])).

tff(c_14788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14783,c_14786])).

tff(c_14789,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_14785])).

tff(c_14978,plain,(
    ! [B_584,A_585] :
      ( r1_tarski(B_584,k2_pre_topc(A_585,B_584))
      | ~ m1_subset_1(B_584,k1_zfmisc_1(u1_struct_0(A_585)))
      | ~ l1_pre_topc(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14985,plain,
    ( r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_14978])).

tff(c_14992,plain,(
    r1_tarski('#skF_3',k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14985])).

tff(c_14813,plain,(
    ! [A_574,B_575] :
      ( k3_subset_1(A_574,k3_subset_1(A_574,B_575)) = B_575
      | ~ m1_subset_1(B_575,k1_zfmisc_1(A_574)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14822,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_14813])).

tff(c_14827,plain,(
    ! [A_576,B_577] :
      ( k4_xboole_0(A_576,B_577) = k3_subset_1(A_576,B_577)
      | ~ m1_subset_1(B_577,k1_zfmisc_1(A_576)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14839,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_14827])).

tff(c_14864,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14839,c_8])).

tff(c_15034,plain,(
    ! [A_587,B_588] :
      ( k2_pre_topc(A_587,B_588) = B_588
      | ~ v4_pre_topc(B_588,A_587)
      | ~ m1_subset_1(B_588,k1_zfmisc_1(u1_struct_0(A_587)))
      | ~ l1_pre_topc(A_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_15417,plain,(
    ! [A_611,A_612] :
      ( k2_pre_topc(A_611,A_612) = A_612
      | ~ v4_pre_topc(A_612,A_611)
      | ~ l1_pre_topc(A_611)
      | ~ r1_tarski(A_612,u1_struct_0(A_611)) ) ),
    inference(resolution,[status(thm)],[c_16,c_15034])).

tff(c_15451,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14864,c_15417])).

tff(c_15479,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15451])).

tff(c_16094,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_15479])).

tff(c_16381,plain,(
    ! [B_651,A_652] :
      ( v4_pre_topc(B_651,A_652)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_652),B_651),A_652)
      | ~ m1_subset_1(B_651,k1_zfmisc_1(u1_struct_0(A_652)))
      | ~ l1_pre_topc(A_652) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_16392,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14822,c_16381])).

tff(c_16397,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14783,c_16392])).

tff(c_16398,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_16094,c_16397])).

tff(c_16404,plain,(
    ~ r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_3'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_16398])).

tff(c_16408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14864,c_16404])).

tff(c_16409,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_15479])).

tff(c_17392,plain,(
    ! [A_684,B_685] :
      ( k3_subset_1(u1_struct_0(A_684),k2_pre_topc(A_684,k3_subset_1(u1_struct_0(A_684),B_685))) = k1_tops_1(A_684,B_685)
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0(A_684)))
      | ~ l1_pre_topc(A_684) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_17419,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_3')) = k1_tops_1('#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16409,c_17392])).

tff(c_17439,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_14822,c_17419])).

tff(c_16571,plain,(
    ! [A_660,B_661] :
      ( k1_tops_1(A_660,k2_pre_topc(A_660,B_661)) = B_661
      | ~ v6_tops_1(B_661,A_660)
      | ~ m1_subset_1(B_661,k1_zfmisc_1(u1_struct_0(A_660)))
      | ~ l1_pre_topc(A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16582,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ v6_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_16571])).

tff(c_16591,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_13814,c_16582])).

tff(c_18328,plain,(
    ! [B_695,A_696] :
      ( v4_tops_1(B_695,A_696)
      | ~ r1_tarski(B_695,k2_pre_topc(A_696,k1_tops_1(A_696,B_695)))
      | ~ r1_tarski(k1_tops_1(A_696,k2_pre_topc(A_696,B_695)),B_695)
      | ~ m1_subset_1(B_695,k1_zfmisc_1(u1_struct_0(A_696)))
      | ~ l1_pre_topc(A_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18350,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16591,c_18328])).

tff(c_18375,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_6,c_14992,c_17439,c_18350])).

tff(c_18377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14789,c_18375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.80  
% 10.01/3.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.80  %$ v6_tops_1 > v4_tops_1 > v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.01/3.80  
% 10.01/3.80  %Foreground sorts:
% 10.01/3.80  
% 10.01/3.80  
% 10.01/3.80  %Background operators:
% 10.01/3.80  
% 10.01/3.80  
% 10.01/3.80  %Foreground operators:
% 10.01/3.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.01/3.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/3.80  tff(v6_tops_1, type, v6_tops_1: ($i * $i) > $o).
% 10.01/3.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.01/3.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.01/3.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/3.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.01/3.80  tff(v4_tops_1, type, v4_tops_1: ($i * $i) > $o).
% 10.01/3.80  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.01/3.80  tff('#skF_2', type, '#skF_2': $i).
% 10.01/3.80  tff('#skF_3', type, '#skF_3': $i).
% 10.01/3.80  tff('#skF_1', type, '#skF_1': $i).
% 10.01/3.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.01/3.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.01/3.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/3.80  tff('#skF_4', type, '#skF_4': $i).
% 10.01/3.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/3.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.01/3.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.01/3.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.01/3.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.01/3.80  
% 10.01/3.83  tff(f_174, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (((v3_pre_topc(D, B) & v4_tops_1(D, B)) => v6_tops_1(D, B)) & (v6_tops_1(C, A) => (v3_pre_topc(C, A) & v4_tops_1(C, A)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_tops_1)).
% 10.01/3.83  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.01/3.83  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.01/3.83  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v6_tops_1(B, A) <=> (B = k1_tops_1(A, k2_pre_topc(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tops_1)).
% 10.01/3.83  tff(f_114, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 10.01/3.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.01/3.83  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.01/3.83  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.01/3.83  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.01/3.83  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.01/3.83  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 10.01/3.83  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.01/3.83  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 10.01/3.83  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_tops_1(B, A) <=> (r1_tarski(k1_tops_1(A, k2_pre_topc(A, B)), B) & r1_tarski(B, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 10.01/3.83  tff(f_106, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 10.01/3.83  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, k1_tops_1(A, B)) = k2_pre_topc(A, k1_tops_1(A, k2_pre_topc(A, k1_tops_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tops_1)).
% 10.01/3.83  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 10.01/3.83  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_14359, plain, (![A_546, B_547]: (m1_subset_1(k2_pre_topc(A_546, B_547), k1_zfmisc_1(u1_struct_0(A_546))) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.83  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.83  tff(c_14380, plain, (![A_546, B_547]: (r1_tarski(k2_pre_topc(A_546, B_547), u1_struct_0(A_546)) | ~m1_subset_1(B_547, k1_zfmisc_1(u1_struct_0(A_546))) | ~l1_pre_topc(A_546))), inference(resolution, [status(thm)], [c_14359, c_14])).
% 10.01/3.83  tff(c_66, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_13832, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 10.01/3.83  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_68, plain, (~v6_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_76, plain, (~v6_tops_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_68])).
% 10.01/3.83  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_332, plain, (![A_81, B_82]: (m1_subset_1(k2_pre_topc(A_81, B_82), k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.83  tff(c_346, plain, (![A_81, B_82]: (r1_tarski(k2_pre_topc(A_81, B_82), u1_struct_0(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_332, c_14])).
% 10.01/3.83  tff(c_111, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 10.01/3.83  tff(c_72, plain, (v3_pre_topc('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_77, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 10.01/3.83  tff(c_1030, plain, (![A_120, B_121]: (k1_tops_1(A_120, k2_pre_topc(A_120, B_121))=B_121 | ~v6_tops_1(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.01/3.83  tff(c_1041, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1030])).
% 10.01/3.83  tff(c_1050, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_77, c_1041])).
% 10.01/3.83  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/3.83  tff(c_802, plain, (![A_108, B_109]: (v3_pre_topc(k1_tops_1(A_108, B_109), A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.01/3.83  tff(c_816, plain, (![A_108, A_9]: (v3_pre_topc(k1_tops_1(A_108, A_9), A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | ~r1_tarski(A_9, u1_struct_0(A_108)))), inference(resolution, [status(thm)], [c_16, c_802])).
% 10.01/3.83  tff(c_1054, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_816])).
% 10.01/3.83  tff(c_1064, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1054])).
% 10.01/3.83  tff(c_1065, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_111, c_1064])).
% 10.01/3.83  tff(c_1073, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_346, c_1065])).
% 10.01/3.83  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1073])).
% 10.01/3.83  tff(c_1079, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 10.01/3.83  tff(c_64, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_1081, plain, (v4_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_64])).
% 10.01/3.83  tff(c_1082, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1081])).
% 10.01/3.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/3.83  tff(c_1249, plain, (![B_134, A_135]: (r1_tarski(B_134, k2_pre_topc(A_135, B_134)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.83  tff(c_1256, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1249])).
% 10.01/3.83  tff(c_1263, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1256])).
% 10.01/3.83  tff(c_1084, plain, (![A_124, B_125]: (k3_subset_1(A_124, k3_subset_1(A_124, B_125))=B_125 | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.83  tff(c_1093, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_54, c_1084])).
% 10.01/3.83  tff(c_1098, plain, (![A_126, B_127]: (k4_xboole_0(A_126, B_127)=k3_subset_1(A_126, B_127) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.83  tff(c_1110, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1098])).
% 10.01/3.83  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.01/3.83  tff(c_1135, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1110, c_8])).
% 10.01/3.83  tff(c_2004, plain, (![B_175, A_176]: (v4_pre_topc(B_175, A_176) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_176), B_175), A_176) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.01/3.83  tff(c_2015, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1093, c_2004])).
% 10.01/3.83  tff(c_2020, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1079, c_2015])).
% 10.01/3.83  tff(c_2143, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2020])).
% 10.01/3.83  tff(c_2146, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_2143])).
% 10.01/3.83  tff(c_2150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1135, c_2146])).
% 10.01/3.83  tff(c_2151, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_2020])).
% 10.01/3.83  tff(c_2152, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2020])).
% 10.01/3.83  tff(c_24, plain, (![A_16, B_18]: (k2_pre_topc(A_16, B_18)=B_18 | ~v4_pre_topc(B_18, A_16) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.01/3.83  tff(c_2157, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2152, c_24])).
% 10.01/3.83  tff(c_2175, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2151, c_2157])).
% 10.01/3.83  tff(c_3425, plain, (![A_221, B_222]: (k3_subset_1(u1_struct_0(A_221), k2_pre_topc(A_221, k3_subset_1(u1_struct_0(A_221), B_222)))=k1_tops_1(A_221, B_222) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.01/3.83  tff(c_3452, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2175, c_3425])).
% 10.01/3.83  tff(c_3472, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_1093, c_3452])).
% 10.01/3.83  tff(c_2207, plain, (![A_181, B_182]: (k1_tops_1(A_181, k2_pre_topc(A_181, B_182))=B_182 | ~v6_tops_1(B_182, A_181) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.01/3.83  tff(c_2220, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_2207])).
% 10.01/3.83  tff(c_2232, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_77, c_2220])).
% 10.01/3.83  tff(c_4199, plain, (![B_229, A_230]: (v4_tops_1(B_229, A_230) | ~r1_tarski(B_229, k2_pre_topc(A_230, k1_tops_1(A_230, B_229))) | ~r1_tarski(k1_tops_1(A_230, k2_pre_topc(A_230, B_229)), B_229) | ~m1_subset_1(B_229, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.01/3.83  tff(c_4224, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2232, c_4199])).
% 10.01/3.83  tff(c_4243, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_6, c_1263, c_3472, c_4224])).
% 10.01/3.83  tff(c_4245, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1082, c_4243])).
% 10.01/3.83  tff(c_4246, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1081])).
% 10.01/3.83  tff(c_32, plain, (![A_22, B_24]: (r1_tarski(k1_tops_1(A_22, k2_pre_topc(A_22, B_24)), B_24) | ~v4_tops_1(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.01/3.83  tff(c_4331, plain, (![B_239, A_240]: (r1_tarski(B_239, k2_pre_topc(A_240, B_239)) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.83  tff(c_4336, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_4331])).
% 10.01/3.83  tff(c_4342, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4336])).
% 10.01/3.83  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k2_pre_topc(A_11, B_12), k1_zfmisc_1(u1_struct_0(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.83  tff(c_38, plain, (![A_28, B_29]: (m1_subset_1(k1_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.01/3.83  tff(c_4250, plain, (![A_231, B_232]: (k3_subset_1(A_231, k3_subset_1(A_231, B_232))=B_232 | ~m1_subset_1(B_232, k1_zfmisc_1(A_231)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.83  tff(c_4258, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_52, c_4250])).
% 10.01/3.83  tff(c_4318, plain, (![A_237, B_238]: (k4_xboole_0(A_237, B_238)=k3_subset_1(A_237, B_238) | ~m1_subset_1(B_238, k1_zfmisc_1(A_237)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.83  tff(c_4329, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_52, c_4318])).
% 10.01/3.83  tff(c_4358, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4329, c_8])).
% 10.01/3.83  tff(c_4247, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_1081])).
% 10.01/3.83  tff(c_1078, plain, (~v4_tops_1('#skF_3', '#skF_1') | v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_66])).
% 10.01/3.83  tff(c_4249, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4247, c_1078])).
% 10.01/3.83  tff(c_5100, plain, (![B_283, A_284]: (v4_pre_topc(B_283, A_284) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_284), B_283), A_284) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.01/3.83  tff(c_5114, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4258, c_5100])).
% 10.01/3.83  tff(c_5118, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4249, c_5114])).
% 10.01/3.83  tff(c_5271, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_5118])).
% 10.01/3.83  tff(c_5274, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_5271])).
% 10.01/3.83  tff(c_5278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4358, c_5274])).
% 10.01/3.83  tff(c_5279, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_5118])).
% 10.01/3.83  tff(c_5280, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_5118])).
% 10.01/3.83  tff(c_5285, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_5280, c_24])).
% 10.01/3.83  tff(c_5303, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5279, c_5285])).
% 10.01/3.83  tff(c_6418, plain, (![A_322, B_323]: (k3_subset_1(u1_struct_0(A_322), k2_pre_topc(A_322, k3_subset_1(u1_struct_0(A_322), B_323)))=k1_tops_1(A_322, B_323) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.01/3.83  tff(c_6445, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5303, c_6418])).
% 10.01/3.83  tff(c_6468, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_4258, c_6445])).
% 10.01/3.83  tff(c_6673, plain, (![A_324, B_325]: (k2_pre_topc(A_324, k1_tops_1(A_324, k2_pre_topc(A_324, k1_tops_1(A_324, B_325))))=k2_pre_topc(A_324, k1_tops_1(A_324, B_325)) | ~m1_subset_1(B_325, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_148])).
% 10.01/3.83  tff(c_6714, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6468, c_6673])).
% 10.01/3.83  tff(c_6740, plain, (k2_pre_topc('#skF_2', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_6468, c_6714])).
% 10.01/3.83  tff(c_4441, plain, (![A_245, B_246]: (m1_subset_1(k2_pre_topc(A_245, B_246), k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.83  tff(c_4455, plain, (![A_245, B_246]: (r1_tarski(k2_pre_topc(A_245, B_246), u1_struct_0(A_245)) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(resolution, [status(thm)], [c_4441, c_14])).
% 10.01/3.83  tff(c_6835, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6740, c_4455])).
% 10.01/3.83  tff(c_6858, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6835])).
% 10.01/3.83  tff(c_8523, plain, (~m1_subset_1(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_6858])).
% 10.01/3.83  tff(c_8526, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_8523])).
% 10.01/3.83  tff(c_8532, plain, (~m1_subset_1(k2_pre_topc('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_8526])).
% 10.01/3.83  tff(c_8572, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_8532])).
% 10.01/3.83  tff(c_8579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_8572])).
% 10.01/3.83  tff(c_8580, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6858])).
% 10.01/3.83  tff(c_6903, plain, (![A_326, B_327, C_328]: (r1_tarski(k1_tops_1(A_326, B_327), k1_tops_1(A_326, C_328)) | ~r1_tarski(B_327, C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(u1_struct_0(A_326))) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_326))) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.01/3.83  tff(c_6917, plain, (![C_328]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_328)) | ~r1_tarski('#skF_4', C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6468, c_6903])).
% 10.01/3.83  tff(c_7069, plain, (![C_330]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_330)) | ~r1_tarski('#skF_4', C_330) | ~m1_subset_1(C_330, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_6917])).
% 10.01/3.83  tff(c_7095, plain, (![A_9]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_9)) | ~r1_tarski('#skF_4', A_9) | ~r1_tarski(A_9, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_7069])).
% 10.01/3.83  tff(c_8583, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_8580, c_7095])).
% 10.01/3.83  tff(c_8601, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4342, c_8583])).
% 10.01/3.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/3.83  tff(c_8623, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_8601, c_2])).
% 10.01/3.83  tff(c_8968, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_8623])).
% 10.01/3.83  tff(c_9015, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_8968])).
% 10.01/3.83  tff(c_9022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_4246, c_9015])).
% 10.01/3.83  tff(c_9023, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_8623])).
% 10.01/3.83  tff(c_34, plain, (![B_27, A_25]: (v6_tops_1(B_27, A_25) | k1_tops_1(A_25, k2_pre_topc(A_25, B_27))!=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.01/3.83  tff(c_9074, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9023, c_34])).
% 10.01/3.83  tff(c_9112, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_9074])).
% 10.01/3.83  tff(c_9114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_9112])).
% 10.01/3.83  tff(c_9116, plain, (~v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_72])).
% 10.01/3.83  tff(c_70, plain, (v4_tops_1('#skF_4', '#skF_2') | v6_tops_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_9117, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 10.01/3.83  tff(c_9118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9116, c_9117])).
% 10.01/3.83  tff(c_9119, plain, (v4_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_70])).
% 10.01/3.83  tff(c_9357, plain, (![B_384, A_385]: (r1_tarski(B_384, k2_pre_topc(A_385, B_384)) | ~m1_subset_1(B_384, k1_zfmisc_1(u1_struct_0(A_385))) | ~l1_pre_topc(A_385))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.83  tff(c_9362, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_9357])).
% 10.01/3.83  tff(c_9368, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9362])).
% 10.01/3.83  tff(c_9156, plain, (![A_371, B_372]: (k4_xboole_0(A_371, B_372)=k3_subset_1(A_371, B_372) | ~m1_subset_1(B_372, k1_zfmisc_1(A_371)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.83  tff(c_9167, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_4')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_52, c_9156])).
% 10.01/3.83  tff(c_9175, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9167, c_8])).
% 10.01/3.83  tff(c_9240, plain, (![A_376, B_377]: (k3_subset_1(A_376, k3_subset_1(A_376, B_377))=B_377 | ~m1_subset_1(B_377, k1_zfmisc_1(A_376)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.83  tff(c_9248, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_52, c_9240])).
% 10.01/3.83  tff(c_11650, plain, (![A_481, B_482]: (k3_subset_1(u1_struct_0(A_481), k2_pre_topc(A_481, k3_subset_1(u1_struct_0(A_481), B_482)))=k1_tops_1(A_481, B_482) | ~m1_subset_1(B_482, k1_zfmisc_1(u1_struct_0(A_481))) | ~l1_pre_topc(A_481))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.01/3.83  tff(c_11688, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9248, c_11650])).
% 10.01/3.83  tff(c_11696, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_11688])).
% 10.01/3.83  tff(c_11993, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_11696])).
% 10.01/3.83  tff(c_11996, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_11993])).
% 10.01/3.83  tff(c_12000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9175, c_11996])).
% 10.01/3.83  tff(c_12001, plain, (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(splitRight, [status(thm)], [c_11696])).
% 10.01/3.83  tff(c_9585, plain, (![A_394, B_395]: (m1_subset_1(k2_pre_topc(A_394, B_395), k1_zfmisc_1(u1_struct_0(A_394))) | ~m1_subset_1(B_395, k1_zfmisc_1(u1_struct_0(A_394))) | ~l1_pre_topc(A_394))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.01/3.83  tff(c_12, plain, (![A_7, B_8]: (k3_subset_1(A_7, k3_subset_1(A_7, B_8))=B_8 | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.83  tff(c_12963, plain, (![A_495, B_496]: (k3_subset_1(u1_struct_0(A_495), k3_subset_1(u1_struct_0(A_495), k2_pre_topc(A_495, B_496)))=k2_pre_topc(A_495, B_496) | ~m1_subset_1(B_496, k1_zfmisc_1(u1_struct_0(A_495))) | ~l1_pre_topc(A_495))), inference(resolution, [status(thm)], [c_9585, c_12])).
% 10.01/3.83  tff(c_12993, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12001, c_12963])).
% 10.01/3.83  tff(c_13024, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')))=k2_pre_topc('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_12993])).
% 10.01/3.83  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k3_subset_1(A_5, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.83  tff(c_13375, plain, (![A_504, B_505]: (k4_xboole_0(u1_struct_0(A_504), k2_pre_topc(A_504, B_505))=k3_subset_1(u1_struct_0(A_504), k2_pre_topc(A_504, B_505)) | ~m1_subset_1(B_505, k1_zfmisc_1(u1_struct_0(A_504))) | ~l1_pre_topc(A_504))), inference(resolution, [status(thm)], [c_9585, c_10])).
% 10.01/3.83  tff(c_13392, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_13375])).
% 10.01/3.83  tff(c_13412, plain, (k4_xboole_0(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12001, c_13392])).
% 10.01/3.83  tff(c_9197, plain, (![B_373, A_374]: (k4_xboole_0(B_373, A_374)=k3_subset_1(B_373, A_374) | ~r1_tarski(A_374, B_373))), inference(resolution, [status(thm)], [c_16, c_9156])).
% 10.01/3.83  tff(c_9321, plain, (![A_382, B_383]: (k4_xboole_0(A_382, k4_xboole_0(A_382, B_383))=k3_subset_1(A_382, k4_xboole_0(A_382, B_383)))), inference(resolution, [status(thm)], [c_8, c_9197])).
% 10.01/3.83  tff(c_9333, plain, (![A_382, B_383]: (r1_tarski(k3_subset_1(A_382, k4_xboole_0(A_382, B_383)), A_382))), inference(superposition, [status(thm), theory('equality')], [c_9321, c_8])).
% 10.01/3.83  tff(c_13440, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), k1_tops_1('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13412, c_9333])).
% 10.01/3.83  tff(c_13460, plain, (r1_tarski(k2_pre_topc('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_13024, c_13440])).
% 10.01/3.83  tff(c_9727, plain, (![A_404, B_405]: (k2_pre_topc(A_404, B_405)=B_405 | ~v4_pre_topc(B_405, A_404) | ~m1_subset_1(B_405, k1_zfmisc_1(u1_struct_0(A_404))) | ~l1_pre_topc(A_404))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.01/3.83  tff(c_9751, plain, (![A_406, A_407]: (k2_pre_topc(A_406, A_407)=A_407 | ~v4_pre_topc(A_407, A_406) | ~l1_pre_topc(A_406) | ~r1_tarski(A_407, u1_struct_0(A_406)))), inference(resolution, [status(thm)], [c_16, c_9727])).
% 10.01/3.83  tff(c_9785, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9175, c_9751])).
% 10.01/3.83  tff(c_9812, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9785])).
% 10.01/3.83  tff(c_10402, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_9812])).
% 10.01/3.83  tff(c_9115, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 10.01/3.83  tff(c_10710, plain, (![B_450, A_451]: (v4_pre_topc(B_450, A_451) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_451), B_450), A_451) | ~m1_subset_1(B_450, k1_zfmisc_1(u1_struct_0(A_451))) | ~l1_pre_topc(A_451))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.01/3.83  tff(c_10727, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9248, c_10710])).
% 10.01/3.83  tff(c_10733, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_9115, c_10727])).
% 10.01/3.83  tff(c_10734, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_10402, c_10733])).
% 10.01/3.83  tff(c_10737, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_10734])).
% 10.01/3.83  tff(c_10741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9175, c_10737])).
% 10.01/3.83  tff(c_10742, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_9812])).
% 10.01/3.83  tff(c_11674, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10742, c_11650])).
% 10.01/3.83  tff(c_11692, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_9248, c_11674])).
% 10.01/3.83  tff(c_12084, plain, (![A_485, B_486, C_487]: (r1_tarski(k1_tops_1(A_485, B_486), k1_tops_1(A_485, C_487)) | ~r1_tarski(B_486, C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(u1_struct_0(A_485))) | ~m1_subset_1(B_486, k1_zfmisc_1(u1_struct_0(A_485))) | ~l1_pre_topc(A_485))), inference(cnfTransformation, [status(thm)], [f_141])).
% 10.01/3.83  tff(c_12092, plain, (![C_487]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_487)) | ~r1_tarski('#skF_4', C_487) | ~m1_subset_1(C_487, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_11692, c_12084])).
% 10.01/3.83  tff(c_13226, plain, (![C_502]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', C_502)) | ~r1_tarski('#skF_4', C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_12092])).
% 10.01/3.83  tff(c_13252, plain, (![A_9]: (r1_tarski('#skF_4', k1_tops_1('#skF_2', A_9)) | ~r1_tarski('#skF_4', A_9) | ~r1_tarski(A_9, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_16, c_13226])).
% 10.01/3.83  tff(c_13465, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))) | ~r1_tarski('#skF_4', k2_pre_topc('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_13460, c_13252])).
% 10.01/3.83  tff(c_13483, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9368, c_13465])).
% 10.01/3.83  tff(c_13541, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4' | ~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(resolution, [status(thm)], [c_13483, c_2])).
% 10.01/3.83  tff(c_13714, plain, (~r1_tarski(k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4')), '#skF_4')), inference(splitLeft, [status(thm)], [c_13541])).
% 10.01/3.83  tff(c_13720, plain, (~v4_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_13714])).
% 10.01/3.83  tff(c_13727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_9119, c_13720])).
% 10.01/3.83  tff(c_13728, plain, (k1_tops_1('#skF_2', k2_pre_topc('#skF_2', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_13541])).
% 10.01/3.83  tff(c_13773, plain, (v6_tops_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13728, c_34])).
% 10.01/3.83  tff(c_13811, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_13773])).
% 10.01/3.83  tff(c_13813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_13811])).
% 10.01/3.83  tff(c_13814, plain, (v6_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 10.01/3.83  tff(c_14715, plain, (![A_568, B_569]: (k1_tops_1(A_568, k2_pre_topc(A_568, B_569))=B_569 | ~v6_tops_1(B_569, A_568) | ~m1_subset_1(B_569, k1_zfmisc_1(u1_struct_0(A_568))) | ~l1_pre_topc(A_568))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.01/3.83  tff(c_14726, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_14715])).
% 10.01/3.83  tff(c_14735, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13814, c_14726])).
% 10.01/3.83  tff(c_14090, plain, (![A_532, B_533]: (v3_pre_topc(k1_tops_1(A_532, B_533), A_532) | ~m1_subset_1(B_533, k1_zfmisc_1(u1_struct_0(A_532))) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.01/3.83  tff(c_14098, plain, (![A_532, A_9]: (v3_pre_topc(k1_tops_1(A_532, A_9), A_532) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | ~r1_tarski(A_9, u1_struct_0(A_532)))), inference(resolution, [status(thm)], [c_16, c_14090])).
% 10.01/3.83  tff(c_14761, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14735, c_14098])).
% 10.01/3.83  tff(c_14770, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_14761])).
% 10.01/3.83  tff(c_14771, plain, (~r1_tarski(k2_pre_topc('#skF_1', '#skF_3'), u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_13832, c_14770])).
% 10.01/3.83  tff(c_14777, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14380, c_14771])).
% 10.01/3.83  tff(c_14781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_14777])).
% 10.01/3.83  tff(c_14783, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 10.01/3.83  tff(c_13815, plain, (v6_tops_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 10.01/3.83  tff(c_62, plain, (~v6_tops_1('#skF_4', '#skF_2') | ~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_174])).
% 10.01/3.83  tff(c_14785, plain, (~v4_tops_1('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13815, c_62])).
% 10.01/3.83  tff(c_14786, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_14785])).
% 10.01/3.83  tff(c_14788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14783, c_14786])).
% 10.01/3.83  tff(c_14789, plain, (~v4_tops_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_14785])).
% 10.01/3.83  tff(c_14978, plain, (![B_584, A_585]: (r1_tarski(B_584, k2_pre_topc(A_585, B_584)) | ~m1_subset_1(B_584, k1_zfmisc_1(u1_struct_0(A_585))) | ~l1_pre_topc(A_585))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.83  tff(c_14985, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_14978])).
% 10.01/3.83  tff(c_14992, plain, (r1_tarski('#skF_3', k2_pre_topc('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14985])).
% 10.01/3.83  tff(c_14813, plain, (![A_574, B_575]: (k3_subset_1(A_574, k3_subset_1(A_574, B_575))=B_575 | ~m1_subset_1(B_575, k1_zfmisc_1(A_574)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/3.83  tff(c_14822, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_54, c_14813])).
% 10.01/3.83  tff(c_14827, plain, (![A_576, B_577]: (k4_xboole_0(A_576, B_577)=k3_subset_1(A_576, B_577) | ~m1_subset_1(B_577, k1_zfmisc_1(A_576)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/3.83  tff(c_14839, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_54, c_14827])).
% 10.01/3.83  tff(c_14864, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14839, c_8])).
% 10.01/3.83  tff(c_15034, plain, (![A_587, B_588]: (k2_pre_topc(A_587, B_588)=B_588 | ~v4_pre_topc(B_588, A_587) | ~m1_subset_1(B_588, k1_zfmisc_1(u1_struct_0(A_587))) | ~l1_pre_topc(A_587))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.01/3.83  tff(c_15417, plain, (![A_611, A_612]: (k2_pre_topc(A_611, A_612)=A_612 | ~v4_pre_topc(A_612, A_611) | ~l1_pre_topc(A_611) | ~r1_tarski(A_612, u1_struct_0(A_611)))), inference(resolution, [status(thm)], [c_16, c_15034])).
% 10.01/3.83  tff(c_15451, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14864, c_15417])).
% 10.01/3.83  tff(c_15479, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15451])).
% 10.01/3.83  tff(c_16094, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_15479])).
% 10.01/3.83  tff(c_16381, plain, (![B_651, A_652]: (v4_pre_topc(B_651, A_652) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_652), B_651), A_652) | ~m1_subset_1(B_651, k1_zfmisc_1(u1_struct_0(A_652))) | ~l1_pre_topc(A_652))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.01/3.83  tff(c_16392, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14822, c_16381])).
% 10.01/3.83  tff(c_16397, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14783, c_16392])).
% 10.01/3.83  tff(c_16398, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_16094, c_16397])).
% 10.01/3.83  tff(c_16404, plain, (~r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_16398])).
% 10.01/3.83  tff(c_16408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14864, c_16404])).
% 10.01/3.83  tff(c_16409, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_15479])).
% 10.01/3.83  tff(c_17392, plain, (![A_684, B_685]: (k3_subset_1(u1_struct_0(A_684), k2_pre_topc(A_684, k3_subset_1(u1_struct_0(A_684), B_685)))=k1_tops_1(A_684, B_685) | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0(A_684))) | ~l1_pre_topc(A_684))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.01/3.83  tff(c_17419, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_3'))=k1_tops_1('#skF_1', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16409, c_17392])).
% 10.01/3.83  tff(c_17439, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_14822, c_17419])).
% 10.01/3.83  tff(c_16571, plain, (![A_660, B_661]: (k1_tops_1(A_660, k2_pre_topc(A_660, B_661))=B_661 | ~v6_tops_1(B_661, A_660) | ~m1_subset_1(B_661, k1_zfmisc_1(u1_struct_0(A_660))) | ~l1_pre_topc(A_660))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.01/3.83  tff(c_16582, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~v6_tops_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_16571])).
% 10.01/3.83  tff(c_16591, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_13814, c_16582])).
% 10.01/3.83  tff(c_18328, plain, (![B_695, A_696]: (v4_tops_1(B_695, A_696) | ~r1_tarski(B_695, k2_pre_topc(A_696, k1_tops_1(A_696, B_695))) | ~r1_tarski(k1_tops_1(A_696, k2_pre_topc(A_696, B_695)), B_695) | ~m1_subset_1(B_695, k1_zfmisc_1(u1_struct_0(A_696))) | ~l1_pre_topc(A_696))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.01/3.83  tff(c_18350, plain, (v4_tops_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', k2_pre_topc('#skF_1', k1_tops_1('#skF_1', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16591, c_18328])).
% 10.01/3.83  tff(c_18375, plain, (v4_tops_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_6, c_14992, c_17439, c_18350])).
% 10.01/3.83  tff(c_18377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14789, c_18375])).
% 10.01/3.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.83  
% 10.01/3.83  Inference rules
% 10.01/3.83  ----------------------
% 10.01/3.83  #Ref     : 0
% 10.01/3.83  #Sup     : 4162
% 10.01/3.83  #Fact    : 0
% 10.01/3.83  #Define  : 0
% 10.01/3.83  #Split   : 120
% 10.01/3.83  #Chain   : 0
% 10.01/3.83  #Close   : 0
% 10.01/3.83  
% 10.01/3.83  Ordering : KBO
% 10.01/3.83  
% 10.01/3.83  Simplification rules
% 10.01/3.83  ----------------------
% 10.01/3.83  #Subsume      : 348
% 10.01/3.83  #Demod        : 4598
% 10.01/3.83  #Tautology    : 1723
% 10.01/3.83  #SimpNegUnit  : 59
% 10.01/3.83  #BackRed      : 47
% 10.01/3.83  
% 10.01/3.83  #Partial instantiations: 0
% 10.01/3.83  #Strategies tried      : 1
% 10.01/3.83  
% 10.01/3.83  Timing (in seconds)
% 10.01/3.83  ----------------------
% 10.01/3.84  Preprocessing        : 0.37
% 10.01/3.84  Parsing              : 0.20
% 10.01/3.84  CNF conversion       : 0.03
% 10.01/3.84  Main loop            : 2.51
% 10.01/3.84  Inferencing          : 0.70
% 10.01/3.84  Reduction            : 1.06
% 10.01/3.84  Demodulation         : 0.81
% 10.01/3.84  BG Simplification    : 0.09
% 10.01/3.84  Subsumption          : 0.46
% 10.01/3.84  Abstraction          : 0.13
% 10.01/3.84  MUC search           : 0.00
% 10.01/3.84  Cooper               : 0.00
% 10.01/3.84  Total                : 2.95
% 10.01/3.84  Index Insertion      : 0.00
% 10.01/3.84  Index Deletion       : 0.00
% 10.01/3.84  Index Matching       : 0.00
% 10.01/3.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
