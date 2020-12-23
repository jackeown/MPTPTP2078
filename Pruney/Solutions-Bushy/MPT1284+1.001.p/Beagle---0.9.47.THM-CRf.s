%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1284+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:43 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 298 expanded)
%              Number of leaves         :   27 ( 117 expanded)
%              Depth                    :   13
%              Number of atoms          :  317 (1261 expanded)
%              Number of equality atoms :   36 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > v4_tops_1 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( ( v4_pre_topc(D,B)
                          & v4_tops_1(D,B) )
                       => v5_tops_1(D,B) )
                      & ( v5_tops_1(C,A)
                       => ( v4_pre_topc(C,A)
                          & v4_tops_1(C,A) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
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

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_tops_1(B,A)
          <=> ( r1_tarski(k1_tops_1(A,k2_pre_topc(A,B)),B)
              & r1_tarski(B,k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(c_44,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1305,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_53,plain,(
    ~ v5_tops_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1023,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k1_tops_1(A_144,B_145),B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1027,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1023])).

tff(c_1033,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1027])).

tff(c_423,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_427,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_423])).

tff(c_433,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_427])).

tff(c_64,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_121,plain,(
    ! [A_48,B_49] :
      ( k2_pre_topc(A_48,k1_tops_1(A_48,B_49)) = B_49
      | ~ v5_tops_1(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_131,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_125])).

tff(c_110,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k1_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( v4_pre_topc(k2_pre_topc(A_11,B_12),A_11)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_164,plain,(
    ! [A_54,B_55] :
      ( v4_pre_topc(k2_pre_topc(A_54,k1_tops_1(A_54,B_55)),A_54)
      | ~ v2_pre_topc(A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_20])).

tff(c_167,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_164])).

tff(c_169,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_167])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_169])).

tff(c_173,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_172,plain,
    ( ~ v4_tops_1('#skF_3','#skF_1')
    | v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_176,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_179,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_tops_1(A_56,B_57),B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_181,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_186,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_181])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_241,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,k1_tops_1(A_64,B_65)) = B_65
      | ~ v5_tops_1(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_245,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_251,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54,c_245])).

tff(c_217,plain,(
    ! [A_62,B_63] :
      ( k2_pre_topc(A_62,B_63) = B_63
      | ~ v4_pre_topc(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_223,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_230,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_173,c_223])).

tff(c_402,plain,(
    ! [B_89,A_90] :
      ( v4_tops_1(B_89,A_90)
      | ~ r1_tarski(B_89,k2_pre_topc(A_90,k1_tops_1(A_90,B_89)))
      | ~ r1_tarski(k1_tops_1(A_90,k2_pre_topc(A_90,B_89)),B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_411,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_402])).

tff(c_416,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_186,c_6,c_251,c_411])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_416])).

tff(c_420,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_42,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_422,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_420,c_42])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tops_1(A_9,B_10),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_419,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_442,plain,(
    ! [A_93,B_94] :
      ( k2_pre_topc(A_93,B_94) = B_94
      | ~ v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_448,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_442])).

tff(c_454,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_419,c_448])).

tff(c_564,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_tarski(k2_pre_topc(A_113,B_114),k2_pre_topc(A_113,C_115))
      | ~ r1_tarski(B_114,C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_578,plain,(
    ! [B_114] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_114),'#skF_4')
      | ~ r1_tarski(B_114,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_564])).

tff(c_612,plain,(
    ! [B_117] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_117),'#skF_4')
      | ~ r1_tarski(B_117,'#skF_4')
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_578])).

tff(c_616,plain,(
    ! [B_10] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_10)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_10),'#skF_4')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_612])).

tff(c_622,plain,(
    ! [B_10] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_10)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_10),'#skF_4')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_616])).

tff(c_555,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,k2_pre_topc(A_112,k1_tops_1(A_112,B_111)))
      | ~ v4_tops_1(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_919,plain,(
    ! [A_140,B_141] :
      ( k2_pre_topc(A_140,k1_tops_1(A_140,B_141)) = B_141
      | ~ r1_tarski(k2_pre_topc(A_140,k1_tops_1(A_140,B_141)),B_141)
      | ~ v4_tops_1(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(resolution,[status(thm)],[c_555,c_2])).

tff(c_927,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_622,c_919])).

tff(c_944,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_433,c_34,c_422,c_927])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v5_tops_1(B_8,A_6)
      | k2_pre_topc(A_6,k1_tops_1(A_6,B_8)) != B_8
      | ~ m1_subset_1(B_8,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_983,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_14])).

tff(c_1008,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_983])).

tff(c_1010,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1008])).

tff(c_1012,plain,(
    ~ v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( v4_tops_1('#skF_4','#skF_2')
    | v5_tops_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1013,plain,(
    v4_tops_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1012,c_48])).

tff(c_1011,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1061,plain,(
    ! [A_150,B_151] :
      ( k2_pre_topc(A_150,B_151) = B_151
      | ~ v4_pre_topc(B_151,A_150)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1070,plain,
    ( k2_pre_topc('#skF_2','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1061])).

tff(c_1077,plain,(
    k2_pre_topc('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1011,c_1070])).

tff(c_1135,plain,(
    ! [A_168,B_169,C_170] :
      ( r1_tarski(k2_pre_topc(A_168,B_169),k2_pre_topc(A_168,C_170))
      | ~ r1_tarski(B_169,C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_168)))
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1143,plain,(
    ! [B_169] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_169),'#skF_4')
      | ~ r1_tarski(B_169,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_1135])).

tff(c_1163,plain,(
    ! [B_172] :
      ( r1_tarski(k2_pre_topc('#skF_2',B_172),'#skF_4')
      | ~ r1_tarski(B_172,'#skF_4')
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1143])).

tff(c_1167,plain,(
    ! [B_10] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_10)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_10),'#skF_4')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_1163])).

tff(c_1173,plain,(
    ! [B_10] :
      ( r1_tarski(k2_pre_topc('#skF_2',k1_tops_1('#skF_2',B_10)),'#skF_4')
      | ~ r1_tarski(k1_tops_1('#skF_2',B_10),'#skF_4')
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1167])).

tff(c_1121,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(B_162,k2_pre_topc(A_163,k1_tops_1(A_163,B_162)))
      | ~ v4_tops_1(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1226,plain,(
    ! [A_181,B_182] :
      ( k2_pre_topc(A_181,k1_tops_1(A_181,B_182)) = B_182
      | ~ r1_tarski(k2_pre_topc(A_181,k1_tops_1(A_181,B_182)),B_182)
      | ~ v4_tops_1(B_182,A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(resolution,[status(thm)],[c_1121,c_2])).

tff(c_1230,plain,
    ( k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4'
    | ~ v4_tops_1('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1173,c_1226])).

tff(c_1237,plain,(
    k2_pre_topc('#skF_2',k1_tops_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1033,c_34,c_1013,c_1230])).

tff(c_1268,plain,
    ( v5_tops_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_14])).

tff(c_1291,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1268])).

tff(c_1293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1291])).

tff(c_1294,plain,(
    v5_tops_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1365,plain,(
    ! [A_193,B_194] :
      ( k2_pre_topc(A_193,k1_tops_1(A_193,B_194)) = B_194
      | ~ v5_tops_1(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_193)))
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1369,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1365])).

tff(c_1375,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1294,c_1369])).

tff(c_1332,plain,(
    ! [A_189,B_190] :
      ( v4_pre_topc(k2_pre_topc(A_189,B_190),A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1435,plain,(
    ! [A_203,B_204] :
      ( v4_pre_topc(k2_pre_topc(A_203,k1_tops_1(A_203,B_204)),A_203)
      | ~ v2_pre_topc(A_203)
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0(A_203)))
      | ~ l1_pre_topc(A_203) ) ),
    inference(resolution,[status(thm)],[c_18,c_1332])).

tff(c_1441,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_1435])).

tff(c_1446,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_1441])).

tff(c_1448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1305,c_1446])).

tff(c_1450,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1295,plain,(
    v5_tops_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ v5_tops_1('#skF_4','#skF_2')
    | ~ v4_tops_1('#skF_3','#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1453,plain,(
    ~ v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1450,c_1295,c_40])).

tff(c_1456,plain,(
    ! [A_205,B_206] :
      ( r1_tarski(k1_tops_1(A_205,B_206),B_206)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1458,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1456])).

tff(c_1463,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1458])).

tff(c_1519,plain,(
    ! [A_215,B_216] :
      ( k2_pre_topc(A_215,k1_tops_1(A_215,B_216)) = B_216
      | ~ v5_tops_1(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1523,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3'
    | ~ v5_tops_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1519])).

tff(c_1529,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1294,c_1523])).

tff(c_1494,plain,(
    ! [A_211,B_212] :
      ( k2_pre_topc(A_211,B_212) = B_212
      | ~ v4_pre_topc(B_212,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1500,plain,
    ( k2_pre_topc('#skF_1','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1494])).

tff(c_1507,plain,(
    k2_pre_topc('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1450,c_1500])).

tff(c_1714,plain,(
    ! [B_238,A_239] :
      ( v4_tops_1(B_238,A_239)
      | ~ r1_tarski(B_238,k2_pre_topc(A_239,k1_tops_1(A_239,B_238)))
      | ~ r1_tarski(k1_tops_1(A_239,k2_pre_topc(A_239,B_238)),B_238)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1726,plain,
    ( v4_tops_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_1714])).

tff(c_1733,plain,(
    v4_tops_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_1463,c_6,c_1529,c_1726])).

tff(c_1735,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1453,c_1733])).

%------------------------------------------------------------------------------
