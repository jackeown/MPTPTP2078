%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:26 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 213 expanded)
%              Number of leaves         :   41 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 692 expanded)
%              Number of equality atoms :   23 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_81,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_138,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tex_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k1_xboole_0
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_121,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_286,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_330,plain,(
    ! [B_77,A_78] :
      ( k4_xboole_0(B_77,A_78) = k3_subset_1(B_77,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(resolution,[status(thm)],[c_28,c_286])).

tff(c_342,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k3_subset_1(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_8,c_330])).

tff(c_348,plain,(
    ! [B_2] : k3_subset_1(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_342])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_599,plain,(
    ! [A_91,B_92] :
      ( k2_pre_topc(A_91,B_92) = B_92
      | ~ v4_pre_topc(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_613,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_599])).

tff(c_619,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = '#skF_3'
    | ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_613])).

tff(c_620,plain,(
    ~ v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_64,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k3_subset_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_71,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_223,plain,(
    ! [A_67,B_68] :
      ( k3_subset_1(A_67,k3_subset_1(A_67,B_68)) = B_68
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_229,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_223])).

tff(c_804,plain,(
    ! [B_105,A_106] :
      ( v4_pre_topc(B_105,A_106)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_106),B_105),A_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_819,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_804])).

tff(c_825,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_71,c_819])).

tff(c_882,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_825])).

tff(c_885,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_20,c_882])).

tff(c_892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_885])).

tff(c_893,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_894,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_825])).

tff(c_1198,plain,(
    ! [B_126,A_127] :
      ( v3_pre_topc(B_126,A_127)
      | ~ v4_pre_topc(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ v3_tdlat_3(A_127)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1201,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_894,c_1198])).

tff(c_1226,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_64,c_893,c_1201])).

tff(c_34,plain,(
    ! [B_25,A_23] :
      ( v4_pre_topc(B_25,A_23)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_23),B_25),A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1237,plain,
    ( v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1226,c_34])).

tff(c_1240,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1237])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_1240])).

tff(c_1243,plain,(
    k2_pre_topc('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_1249,plain,(
    ! [A_128,B_129] :
      ( k2_pre_topc(A_128,B_129) = u1_struct_0(A_128)
      | ~ v1_tops_1(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1263,plain,
    ( k2_pre_topc('#skF_2','#skF_3') = u1_struct_0('#skF_2')
    | ~ v1_tops_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1249])).

tff(c_1269,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1243,c_1263])).

tff(c_1270,plain,(
    ~ v1_tops_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1269])).

tff(c_56,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1966,plain,(
    ! [B_166,A_167] :
      ( v1_tops_1(B_166,A_167)
      | ~ v3_tex_2(B_166,A_167)
      | ~ v3_pre_topc(B_166,A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1991,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1966])).

tff(c_2003,plain,
    ( v1_tops_1('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_71,c_56,c_1991])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1270,c_2003])).

tff(c_2006,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1269])).

tff(c_54,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_171,plain,(
    ! [B_57,A_58] :
      ( ~ v1_subset_1(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_177,plain,
    ( ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_171])).

tff(c_181,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_177])).

tff(c_540,plain,(
    ! [A_88,B_89] :
      ( ~ v1_xboole_0(k3_subset_1(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88))
      | ~ v1_subset_1(B_89,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_552,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_540])).

tff(c_558,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_552])).

tff(c_559,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_558])).

tff(c_2008,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2006,c_559])).

tff(c_2021,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_348,c_2008])).

tff(c_2023,plain,(
    ~ v3_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2022,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3282,plain,(
    ! [B_260,A_261] :
      ( v3_pre_topc(B_260,A_261)
      | ~ v4_pre_topc(B_260,A_261)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ v3_tdlat_3(A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3307,plain,
    ( v3_pre_topc('#skF_3','#skF_2')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_3282])).

tff(c_3318,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_64,c_2022,c_3307])).

tff(c_3320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2023,c_3318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.89  
% 4.39/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.89  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.39/1.89  
% 4.39/1.89  %Foreground sorts:
% 4.39/1.89  
% 4.39/1.89  
% 4.39/1.89  %Background operators:
% 4.39/1.89  
% 4.39/1.89  
% 4.39/1.89  %Foreground operators:
% 4.39/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.39/1.89  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.89  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.39/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.39/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.39/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.39/1.89  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.39/1.89  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.39/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.39/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.39/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.89  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.39/1.89  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.39/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.39/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.39/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.39/1.89  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.39/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.89  
% 4.39/1.91  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.39/1.91  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.39/1.91  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.39/1.91  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.39/1.91  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.39/1.91  tff(f_160, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tex_2)).
% 4.39/1.91  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.39/1.91  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.39/1.91  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.39/1.91  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 4.39/1.91  tff(f_122, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.39/1.91  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 4.39/1.91  tff(f_138, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_tex_2)).
% 4.39/1.91  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_subset_1)).
% 4.39/1.91  tff(f_109, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tex_2)).
% 4.39/1.91  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.39/1.91  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.91  tff(c_109, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k1_xboole_0 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.39/1.91  tff(c_121, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_109])).
% 4.39/1.91  tff(c_28, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.39/1.91  tff(c_286, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.39/1.91  tff(c_330, plain, (![B_77, A_78]: (k4_xboole_0(B_77, A_78)=k3_subset_1(B_77, A_78) | ~r1_tarski(A_78, B_77))), inference(resolution, [status(thm)], [c_28, c_286])).
% 4.39/1.91  tff(c_342, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k3_subset_1(B_2, B_2))), inference(resolution, [status(thm)], [c_8, c_330])).
% 4.39/1.91  tff(c_348, plain, (![B_2]: (k3_subset_1(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_342])).
% 4.39/1.91  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_599, plain, (![A_91, B_92]: (k2_pre_topc(A_91, B_92)=B_92 | ~v4_pre_topc(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.39/1.91  tff(c_613, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_599])).
% 4.39/1.91  tff(c_619, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3' | ~v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_613])).
% 4.39/1.91  tff(c_620, plain, (~v4_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_619])).
% 4.39/1.91  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_64, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(k3_subset_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.39/1.91  tff(c_58, plain, (v4_pre_topc('#skF_3', '#skF_2') | v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_71, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 4.39/1.91  tff(c_223, plain, (![A_67, B_68]: (k3_subset_1(A_67, k3_subset_1(A_67, B_68))=B_68 | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.39/1.91  tff(c_229, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_60, c_223])).
% 4.39/1.91  tff(c_804, plain, (![B_105, A_106]: (v4_pre_topc(B_105, A_106) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_106), B_105), A_106) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.39/1.91  tff(c_819, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_229, c_804])).
% 4.39/1.91  tff(c_825, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_71, c_819])).
% 4.39/1.91  tff(c_882, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_825])).
% 4.39/1.91  tff(c_885, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_20, c_882])).
% 4.39/1.91  tff(c_892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_885])).
% 4.39/1.91  tff(c_893, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_825])).
% 4.39/1.91  tff(c_894, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_825])).
% 4.39/1.91  tff(c_1198, plain, (![B_126, A_127]: (v3_pre_topc(B_126, A_127) | ~v4_pre_topc(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~v3_tdlat_3(A_127) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.39/1.91  tff(c_1201, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_894, c_1198])).
% 4.39/1.91  tff(c_1226, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_64, c_893, c_1201])).
% 4.39/1.91  tff(c_34, plain, (![B_25, A_23]: (v4_pre_topc(B_25, A_23) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_23), B_25), A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.39/1.91  tff(c_1237, plain, (v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1226, c_34])).
% 4.39/1.91  tff(c_1240, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1237])).
% 4.39/1.91  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_1240])).
% 4.39/1.91  tff(c_1243, plain, (k2_pre_topc('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_619])).
% 4.39/1.91  tff(c_1249, plain, (![A_128, B_129]: (k2_pre_topc(A_128, B_129)=u1_struct_0(A_128) | ~v1_tops_1(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.39/1.91  tff(c_1263, plain, (k2_pre_topc('#skF_2', '#skF_3')=u1_struct_0('#skF_2') | ~v1_tops_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1249])).
% 4.39/1.91  tff(c_1269, plain, (u1_struct_0('#skF_2')='#skF_3' | ~v1_tops_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1243, c_1263])).
% 4.39/1.91  tff(c_1270, plain, (~v1_tops_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_1269])).
% 4.39/1.91  tff(c_56, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_1966, plain, (![B_166, A_167]: (v1_tops_1(B_166, A_167) | ~v3_tex_2(B_166, A_167) | ~v3_pre_topc(B_166, A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.39/1.91  tff(c_1991, plain, (v1_tops_1('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1966])).
% 4.39/1.91  tff(c_2003, plain, (v1_tops_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_71, c_56, c_1991])).
% 4.39/1.91  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1270, c_2003])).
% 4.39/1.91  tff(c_2006, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1269])).
% 4.39/1.91  tff(c_54, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.39/1.91  tff(c_171, plain, (![B_57, A_58]: (~v1_subset_1(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.39/1.91  tff(c_177, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_171])).
% 4.39/1.91  tff(c_181, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_177])).
% 4.39/1.91  tff(c_540, plain, (![A_88, B_89]: (~v1_xboole_0(k3_subset_1(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)) | ~v1_subset_1(B_89, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.39/1.91  tff(c_552, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_540])).
% 4.39/1.91  tff(c_558, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_552])).
% 4.39/1.91  tff(c_559, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_2'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_181, c_558])).
% 4.39/1.91  tff(c_2008, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2006, c_559])).
% 4.39/1.91  tff(c_2021, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_348, c_2008])).
% 4.39/1.91  tff(c_2023, plain, (~v3_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 4.39/1.91  tff(c_2022, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 4.39/1.91  tff(c_3282, plain, (![B_260, A_261]: (v3_pre_topc(B_260, A_261) | ~v4_pre_topc(B_260, A_261) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_261))) | ~v3_tdlat_3(A_261) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.39/1.91  tff(c_3307, plain, (v3_pre_topc('#skF_3', '#skF_2') | ~v4_pre_topc('#skF_3', '#skF_2') | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_3282])).
% 4.39/1.91  tff(c_3318, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_64, c_2022, c_3307])).
% 4.39/1.91  tff(c_3320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2023, c_3318])).
% 4.39/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.91  
% 4.39/1.91  Inference rules
% 4.39/1.91  ----------------------
% 4.39/1.91  #Ref     : 0
% 4.39/1.91  #Sup     : 691
% 4.39/1.91  #Fact    : 0
% 4.39/1.91  #Define  : 0
% 4.39/1.91  #Split   : 16
% 4.39/1.91  #Chain   : 0
% 4.39/1.91  #Close   : 0
% 4.39/1.91  
% 4.39/1.91  Ordering : KBO
% 4.39/1.91  
% 4.39/1.91  Simplification rules
% 4.39/1.91  ----------------------
% 4.39/1.91  #Subsume      : 67
% 4.39/1.91  #Demod        : 399
% 4.39/1.91  #Tautology    : 335
% 4.39/1.91  #SimpNegUnit  : 19
% 4.39/1.91  #BackRed      : 13
% 4.39/1.91  
% 4.39/1.91  #Partial instantiations: 0
% 4.39/1.91  #Strategies tried      : 1
% 4.39/1.91  
% 4.39/1.91  Timing (in seconds)
% 4.39/1.91  ----------------------
% 4.83/1.91  Preprocessing        : 0.36
% 4.83/1.91  Parsing              : 0.20
% 4.83/1.91  CNF conversion       : 0.02
% 4.83/1.91  Main loop            : 0.72
% 4.83/1.91  Inferencing          : 0.26
% 4.83/1.91  Reduction            : 0.24
% 4.83/1.91  Demodulation         : 0.17
% 4.83/1.91  BG Simplification    : 0.03
% 4.83/1.91  Subsumption          : 0.12
% 4.83/1.91  Abstraction          : 0.04
% 4.83/1.91  MUC search           : 0.00
% 4.83/1.91  Cooper               : 0.00
% 4.83/1.91  Total                : 1.12
% 4.83/1.91  Index Insertion      : 0.00
% 4.83/1.91  Index Deletion       : 0.00
% 4.83/1.91  Index Matching       : 0.00
% 4.83/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
