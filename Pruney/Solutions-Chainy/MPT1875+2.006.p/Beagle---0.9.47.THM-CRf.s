%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 272 expanded)
%              Number of leaves         :   47 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  234 ( 637 expanded)
%              Number of equality atoms :   30 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_tex_2(B,A)
                  | v2_tex_2(C,A) )
               => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_18,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k2_subset_1(A_11),k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [A_11] : m1_subset_1(A_11,k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_54,plain,(
    ! [A_43] :
      ( v2_tex_2(u1_struct_0(A_43),A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ m1_subset_1(u1_struct_0(A_43),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_77,plain,(
    ! [A_43] :
      ( v2_tex_2(u1_struct_0(A_43),A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ l1_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_54])).

tff(c_64,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_390,plain,(
    ! [A_112,B_113] :
      ( u1_struct_0(k1_pre_topc(A_112,B_113)) = B_113
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_400,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_390])).

tff(c_409,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_400])).

tff(c_218,plain,(
    ! [A_87,B_88] :
      ( v1_pre_topc(k1_pre_topc(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,(
    ! [A_87] :
      ( v1_pre_topc(k1_pre_topc(A_87,u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_73,c_218])).

tff(c_432,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_2'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_234])).

tff(c_563,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_432])).

tff(c_565,plain,(
    ! [A_121,B_122] :
      ( m1_pre_topc(k1_pre_topc(A_121,B_122),A_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_578,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_565])).

tff(c_586,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_578])).

tff(c_34,plain,(
    ! [B_24,A_22] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_590,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_586,c_34])).

tff(c_593,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_590])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_593])).

tff(c_597,plain,(
    l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_432])).

tff(c_32,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_637,plain,(
    ! [A_124,B_125] :
      ( m1_pre_topc(k1_pre_topc(A_124,B_125),A_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_652,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_637])).

tff(c_662,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_652])).

tff(c_36,plain,(
    ! [A_25] :
      ( v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | ~ v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_438,plain,
    ( v1_xboole_0('#skF_2')
    | ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_36])).

tff(c_598,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_438])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_44,plain,(
    ! [B_35,A_33] :
      ( v1_tdlat_3(B_35)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v1_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_667,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v1_tdlat_3('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_662,c_44])).

tff(c_676,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_667])).

tff(c_677,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_676])).

tff(c_40,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1084,plain,(
    ! [B_155,A_156] :
      ( v2_tex_2(u1_struct_0(B_155),A_156)
      | ~ v1_tdlat_3(B_155)
      | ~ m1_subset_1(u1_struct_0(B_155),k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ m1_pre_topc(B_155,A_156)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2996,plain,(
    ! [B_235,A_236] :
      ( v2_tex_2(u1_struct_0(B_235),A_236)
      | ~ v1_tdlat_3(B_235)
      | v2_struct_0(B_235)
      | v2_struct_0(A_236)
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(resolution,[status(thm)],[c_40,c_1084])).

tff(c_3028,plain,(
    ! [A_236] :
      ( v2_tex_2('#skF_2',A_236)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(A_236)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_2996])).

tff(c_3037,plain,(
    ! [A_236] :
      ( v2_tex_2('#skF_2',A_236)
      | v2_struct_0(k1_pre_topc('#skF_1','#skF_2'))
      | v2_struct_0(A_236)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_3028])).

tff(c_3039,plain,(
    ! [A_237] :
      ( v2_tex_2('#skF_2',A_237)
      | v2_struct_0(A_237)
      | ~ m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_3037])).

tff(c_3042,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_662,c_3039])).

tff(c_3045,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3042])).

tff(c_3047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_3045])).

tff(c_3048,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_438])).

tff(c_3055,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3048])).

tff(c_3059,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_3055])).

tff(c_3063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_3059])).

tff(c_3064,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3048])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3069,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3064,c_2])).

tff(c_24,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3086,plain,(
    ! [A_15] : m1_subset_1('#skF_2',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3069,c_24])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [B_3] : k4_xboole_0(B_3,B_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_101,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = A_66
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [B_3] : k3_xboole_0(B_3,B_3) = B_3 ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_146,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)) = k3_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [B_3] : k4_xboole_0(B_3,k1_xboole_0) = k3_xboole_0(B_3,B_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_146])).

tff(c_165,plain,(
    ! [B_77] : k4_xboole_0(B_77,k1_xboole_0) = B_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_161])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [B_77] : k4_xboole_0(B_77,B_77) = k3_xboole_0(B_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_16])).

tff(c_184,plain,(
    ! [B_77] : k3_xboole_0(B_77,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_171])).

tff(c_376,plain,(
    ! [A_109,B_110,C_111] :
      ( k9_subset_1(A_109,B_110,C_111) = k3_xboole_0(B_110,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_380,plain,(
    ! [A_15,B_110] : k9_subset_1(A_15,B_110,k1_xboole_0) = k3_xboole_0(B_110,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_376])).

tff(c_387,plain,(
    ! [A_15,B_110] : k9_subset_1(A_15,B_110,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_380])).

tff(c_3071,plain,(
    ! [A_15,B_110] : k9_subset_1(A_15,B_110,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3069,c_3069,c_387])).

tff(c_4154,plain,(
    ! [B_291,A_292,C_293] :
      ( ~ v2_tex_2(B_291,A_292)
      | v2_tex_2(k9_subset_1(u1_struct_0(A_292),B_291,C_293),A_292)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_4176,plain,(
    ! [B_110,A_292] :
      ( ~ v2_tex_2(B_110,A_292)
      | v2_tex_2('#skF_2',A_292)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_292)))
      | ~ l1_pre_topc(A_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3071,c_4154])).

tff(c_4830,plain,(
    ! [B_321,A_322] :
      ( ~ v2_tex_2(B_321,A_322)
      | v2_tex_2('#skF_2',A_322)
      | ~ m1_subset_1(B_321,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3086,c_4176])).

tff(c_4880,plain,(
    ! [A_323] :
      ( ~ v2_tex_2(u1_struct_0(A_323),A_323)
      | v2_tex_2('#skF_2',A_323)
      | ~ l1_pre_topc(A_323) ) ),
    inference(resolution,[status(thm)],[c_73,c_4830])).

tff(c_5012,plain,(
    ! [A_327] :
      ( v2_tex_2('#skF_2',A_327)
      | ~ v1_tdlat_3(A_327)
      | ~ l1_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_77,c_4880])).

tff(c_5015,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5012,c_62])).

tff(c_5018,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_5015])).

tff(c_5020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:38:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.32/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.27  
% 6.32/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.28  %$ v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.32/2.28  
% 6.32/2.28  %Foreground sorts:
% 6.32/2.28  
% 6.32/2.28  
% 6.32/2.28  %Background operators:
% 6.32/2.28  
% 6.32/2.28  
% 6.32/2.28  %Foreground operators:
% 6.32/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.32/2.28  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 6.32/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.32/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.32/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.32/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.32/2.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.32/2.28  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.32/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.32/2.28  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.32/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.32/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.32/2.28  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.32/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.32/2.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.32/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.32/2.28  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.32/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.32/2.28  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.32/2.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.32/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.32/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.32/2.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.32/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.32/2.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.32/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.32/2.28  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 6.32/2.28  
% 6.64/2.31  tff(f_187, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 6.64/2.31  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.64/2.31  tff(f_49, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.64/2.31  tff(f_158, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 6.64/2.31  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 6.64/2.31  tff(f_69, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 6.64/2.31  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.64/2.31  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.64/2.31  tff(f_86, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 6.64/2.31  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 6.64/2.31  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.64/2.31  tff(f_144, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 6.64/2.31  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.64/2.31  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.64/2.31  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.64/2.31  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.64/2.31  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.64/2.31  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.64/2.31  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.64/2.31  tff(f_172, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 6.64/2.31  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_66, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_68, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_18, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.64/2.31  tff(c_20, plain, (![A_11]: (m1_subset_1(k2_subset_1(A_11), k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.64/2.31  tff(c_73, plain, (![A_11]: (m1_subset_1(A_11, k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 6.64/2.31  tff(c_54, plain, (![A_43]: (v2_tex_2(u1_struct_0(A_43), A_43) | ~v1_tdlat_3(A_43) | ~m1_subset_1(u1_struct_0(A_43), k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.64/2.31  tff(c_77, plain, (![A_43]: (v2_tex_2(u1_struct_0(A_43), A_43) | ~v1_tdlat_3(A_43) | ~l1_pre_topc(A_43) | v2_struct_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_54])).
% 6.64/2.31  tff(c_64, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_390, plain, (![A_112, B_113]: (u1_struct_0(k1_pre_topc(A_112, B_113))=B_113 | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.64/2.31  tff(c_400, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_390])).
% 6.64/2.31  tff(c_409, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_400])).
% 6.64/2.31  tff(c_218, plain, (![A_87, B_88]: (v1_pre_topc(k1_pre_topc(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.64/2.31  tff(c_234, plain, (![A_87]: (v1_pre_topc(k1_pre_topc(A_87, u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_73, c_218])).
% 6.64/2.31  tff(c_432, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_2')) | ~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_234])).
% 6.64/2.31  tff(c_563, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_432])).
% 6.64/2.31  tff(c_565, plain, (![A_121, B_122]: (m1_pre_topc(k1_pre_topc(A_121, B_122), A_121) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_121))) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.64/2.31  tff(c_578, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_565])).
% 6.64/2.31  tff(c_586, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_578])).
% 6.64/2.31  tff(c_34, plain, (![B_24, A_22]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.64/2.31  tff(c_590, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_586, c_34])).
% 6.64/2.31  tff(c_593, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_590])).
% 6.64/2.31  tff(c_595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_563, c_593])).
% 6.64/2.31  tff(c_597, plain, (l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_432])).
% 6.64/2.31  tff(c_32, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.64/2.31  tff(c_62, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_637, plain, (![A_124, B_125]: (m1_pre_topc(k1_pre_topc(A_124, B_125), A_124) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.64/2.31  tff(c_652, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_637])).
% 6.64/2.31  tff(c_662, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_652])).
% 6.64/2.31  tff(c_36, plain, (![A_25]: (v1_xboole_0(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | ~v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.64/2.31  tff(c_438, plain, (v1_xboole_0('#skF_2') | ~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | ~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_36])).
% 6.64/2.31  tff(c_598, plain, (~v2_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_438])).
% 6.64/2.31  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.64/2.31  tff(c_44, plain, (![B_35, A_33]: (v1_tdlat_3(B_35) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33) | ~v1_tdlat_3(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.64/2.31  tff(c_667, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v1_tdlat_3('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_662, c_44])).
% 6.64/2.31  tff(c_676, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_667])).
% 6.64/2.31  tff(c_677, plain, (v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_676])).
% 6.64/2.31  tff(c_40, plain, (![B_31, A_29]: (m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.64/2.31  tff(c_1084, plain, (![B_155, A_156]: (v2_tex_2(u1_struct_0(B_155), A_156) | ~v1_tdlat_3(B_155) | ~m1_subset_1(u1_struct_0(B_155), k1_zfmisc_1(u1_struct_0(A_156))) | ~m1_pre_topc(B_155, A_156) | v2_struct_0(B_155) | ~l1_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.64/2.31  tff(c_2996, plain, (![B_235, A_236]: (v2_tex_2(u1_struct_0(B_235), A_236) | ~v1_tdlat_3(B_235) | v2_struct_0(B_235) | v2_struct_0(A_236) | ~m1_pre_topc(B_235, A_236) | ~l1_pre_topc(A_236))), inference(resolution, [status(thm)], [c_40, c_1084])).
% 6.64/2.31  tff(c_3028, plain, (![A_236]: (v2_tex_2('#skF_2', A_236) | ~v1_tdlat_3(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(A_236) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_236) | ~l1_pre_topc(A_236))), inference(superposition, [status(thm), theory('equality')], [c_409, c_2996])).
% 6.64/2.31  tff(c_3037, plain, (![A_236]: (v2_tex_2('#skF_2', A_236) | v2_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v2_struct_0(A_236) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_236) | ~l1_pre_topc(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_3028])).
% 6.64/2.31  tff(c_3039, plain, (![A_237]: (v2_tex_2('#skF_2', A_237) | v2_struct_0(A_237) | ~m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), A_237) | ~l1_pre_topc(A_237))), inference(negUnitSimplification, [status(thm)], [c_598, c_3037])).
% 6.64/2.31  tff(c_3042, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_662, c_3039])).
% 6.64/2.31  tff(c_3045, plain, (v2_tex_2('#skF_2', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3042])).
% 6.64/2.31  tff(c_3047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_3045])).
% 6.64/2.31  tff(c_3048, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2')) | v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_438])).
% 6.64/2.31  tff(c_3055, plain, (~l1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3048])).
% 6.64/2.31  tff(c_3059, plain, (~l1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_3055])).
% 6.64/2.31  tff(c_3063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_597, c_3059])).
% 6.64/2.31  tff(c_3064, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_3048])).
% 6.64/2.31  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.64/2.31  tff(c_3069, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3064, c_2])).
% 6.64/2.31  tff(c_24, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.64/2.31  tff(c_3086, plain, (![A_15]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_3069, c_24])).
% 6.64/2.31  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.64/2.31  tff(c_119, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.64/2.31  tff(c_127, plain, (![B_3]: (k4_xboole_0(B_3, B_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_119])).
% 6.64/2.31  tff(c_101, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=A_66 | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.64/2.31  tff(c_109, plain, (![B_3]: (k3_xboole_0(B_3, B_3)=B_3)), inference(resolution, [status(thm)], [c_8, c_101])).
% 6.64/2.31  tff(c_146, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))=k3_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.64/2.31  tff(c_161, plain, (![B_3]: (k4_xboole_0(B_3, k1_xboole_0)=k3_xboole_0(B_3, B_3))), inference(superposition, [status(thm), theory('equality')], [c_127, c_146])).
% 6.64/2.31  tff(c_165, plain, (![B_77]: (k4_xboole_0(B_77, k1_xboole_0)=B_77)), inference(demodulation, [status(thm), theory('equality')], [c_109, c_161])).
% 6.64/2.31  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.64/2.31  tff(c_171, plain, (![B_77]: (k4_xboole_0(B_77, B_77)=k3_xboole_0(B_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_16])).
% 6.64/2.31  tff(c_184, plain, (![B_77]: (k3_xboole_0(B_77, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_171])).
% 6.64/2.31  tff(c_376, plain, (![A_109, B_110, C_111]: (k9_subset_1(A_109, B_110, C_111)=k3_xboole_0(B_110, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.64/2.31  tff(c_380, plain, (![A_15, B_110]: (k9_subset_1(A_15, B_110, k1_xboole_0)=k3_xboole_0(B_110, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_376])).
% 6.64/2.31  tff(c_387, plain, (![A_15, B_110]: (k9_subset_1(A_15, B_110, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184, c_380])).
% 6.64/2.31  tff(c_3071, plain, (![A_15, B_110]: (k9_subset_1(A_15, B_110, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3069, c_3069, c_387])).
% 6.64/2.31  tff(c_4154, plain, (![B_291, A_292, C_293]: (~v2_tex_2(B_291, A_292) | v2_tex_2(k9_subset_1(u1_struct_0(A_292), B_291, C_293), A_292) | ~m1_subset_1(C_293, k1_zfmisc_1(u1_struct_0(A_292))) | ~m1_subset_1(B_291, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.64/2.31  tff(c_4176, plain, (![B_110, A_292]: (~v2_tex_2(B_110, A_292) | v2_tex_2('#skF_2', A_292) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_292))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_292))) | ~l1_pre_topc(A_292))), inference(superposition, [status(thm), theory('equality')], [c_3071, c_4154])).
% 6.64/2.31  tff(c_4830, plain, (![B_321, A_322]: (~v2_tex_2(B_321, A_322) | v2_tex_2('#skF_2', A_322) | ~m1_subset_1(B_321, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(demodulation, [status(thm), theory('equality')], [c_3086, c_4176])).
% 6.64/2.31  tff(c_4880, plain, (![A_323]: (~v2_tex_2(u1_struct_0(A_323), A_323) | v2_tex_2('#skF_2', A_323) | ~l1_pre_topc(A_323))), inference(resolution, [status(thm)], [c_73, c_4830])).
% 6.64/2.31  tff(c_5012, plain, (![A_327]: (v2_tex_2('#skF_2', A_327) | ~v1_tdlat_3(A_327) | ~l1_pre_topc(A_327) | v2_struct_0(A_327))), inference(resolution, [status(thm)], [c_77, c_4880])).
% 6.64/2.31  tff(c_5015, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5012, c_62])).
% 6.64/2.31  tff(c_5018, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_5015])).
% 6.64/2.31  tff(c_5020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_5018])).
% 6.64/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.64/2.31  
% 6.64/2.31  Inference rules
% 6.64/2.31  ----------------------
% 6.64/2.31  #Ref     : 0
% 6.64/2.31  #Sup     : 1197
% 6.64/2.31  #Fact    : 0
% 6.64/2.31  #Define  : 0
% 6.64/2.31  #Split   : 11
% 6.64/2.31  #Chain   : 0
% 6.64/2.31  #Close   : 0
% 6.64/2.31  
% 6.64/2.31  Ordering : KBO
% 6.64/2.31  
% 6.64/2.31  Simplification rules
% 6.64/2.31  ----------------------
% 6.64/2.31  #Subsume      : 126
% 6.64/2.31  #Demod        : 874
% 6.64/2.31  #Tautology    : 424
% 6.64/2.31  #SimpNegUnit  : 32
% 6.64/2.31  #BackRed      : 18
% 6.64/2.31  
% 6.64/2.31  #Partial instantiations: 0
% 6.64/2.31  #Strategies tried      : 1
% 6.64/2.31  
% 6.64/2.31  Timing (in seconds)
% 6.64/2.31  ----------------------
% 6.64/2.31  Preprocessing        : 0.37
% 6.64/2.31  Parsing              : 0.21
% 6.64/2.31  CNF conversion       : 0.02
% 6.64/2.31  Main loop            : 1.10
% 6.64/2.31  Inferencing          : 0.36
% 6.64/2.31  Reduction            : 0.40
% 6.64/2.31  Demodulation         : 0.28
% 6.64/2.31  BG Simplification    : 0.05
% 6.64/2.31  Subsumption          : 0.23
% 6.64/2.31  Abstraction          : 0.05
% 6.64/2.31  MUC search           : 0.00
% 6.64/2.31  Cooper               : 0.00
% 6.64/2.31  Total                : 1.53
% 6.64/2.31  Index Insertion      : 0.00
% 6.64/2.31  Index Deletion       : 0.00
% 6.64/2.32  Index Matching       : 0.00
% 6.64/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
