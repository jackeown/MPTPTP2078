%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:57 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 191 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :  222 ( 831 expanded)
%              Number of equality atoms :   12 (  78 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_pre_topc(C,k8_tmap_1(A,B))
               => ( u1_struct_0(C) = u1_struct_0(B)
                 => ( v1_tsep_1(C,k8_tmap_1(A,B))
                    & m1_pre_topc(C,k8_tmap_1(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v2_pre_topc(k8_tmap_1(A_4,B_5))
      | ~ m1_pre_topc(B_5,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_26,plain,
    ( ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( l1_pre_topc(k8_tmap_1(A_4,B_5))
      | ~ m1_pre_topc(B_5,A_4)
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_134,plain,(
    ! [A_53,B_54] :
      ( u1_struct_0(k8_tmap_1(A_53,B_54)) = u1_struct_0(A_53)
      | ~ m1_pre_topc(B_54,A_53)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [B_25,A_23] :
      ( m1_subset_1(u1_struct_0(B_25),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_380,plain,(
    ! [B_83,A_84,B_85] :
      ( m1_subset_1(u1_struct_0(B_83),k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_pre_topc(B_83,k8_tmap_1(A_84,B_85))
      | ~ l1_pre_topc(k8_tmap_1(A_84,B_85))
      | ~ m1_pre_topc(B_85,A_84)
      | v2_struct_0(B_85)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_24])).

tff(c_382,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_380])).

tff(c_385,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_382])).

tff(c_386,plain,
    ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_34,c_385])).

tff(c_410,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_413,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_410])).

tff(c_416,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_413])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_416])).

tff(c_420,plain,(
    l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_419,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_28,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_47,plain,(
    ! [B_30,A_31] :
      ( m1_subset_1(u1_struct_0(B_30),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_30,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc('#skF_2',A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_47])).

tff(c_226,plain,(
    ! [A_65,B_66] :
      ( k5_tmap_1(A_65,u1_struct_0(B_66)) = u1_pre_topc(k8_tmap_1(A_65,B_66))
      | ~ m1_subset_1(u1_struct_0(B_66),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc(B_66,A_65)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_241,plain,(
    ! [A_65] :
      ( k5_tmap_1(A_65,u1_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1(A_65,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc('#skF_2',A_65)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_226])).

tff(c_247,plain,(
    ! [A_65] :
      ( k5_tmap_1(A_65,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_65,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ m1_pre_topc('#skF_2',A_65)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_241])).

tff(c_276,plain,(
    ! [A_71] :
      ( k5_tmap_1(A_71,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_71,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_pre_topc('#skF_2',A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_247])).

tff(c_298,plain,(
    ! [A_73] :
      ( k5_tmap_1(A_73,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_73,'#skF_2'))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc('#skF_2',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_50,c_276])).

tff(c_115,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,k5_tmap_1(A_50,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_122,plain,(
    ! [A_31] :
      ( r2_hidden(u1_struct_0('#skF_3'),k5_tmap_1(A_31,u1_struct_0('#skF_3')))
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31)
      | ~ m1_pre_topc('#skF_2',A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_304,plain,(
    ! [A_73] :
      ( r2_hidden(u1_struct_0('#skF_3'),u1_pre_topc(k8_tmap_1(A_73,'#skF_2')))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc('#skF_2',A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc('#skF_2',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_122])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_387,plain,(
    ! [B_86,A_87,B_88] :
      ( v3_pre_topc(B_86,k8_tmap_1(A_87,B_88))
      | ~ r2_hidden(B_86,u1_pre_topc(k8_tmap_1(A_87,B_88)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(k8_tmap_1(A_87,B_88))
      | ~ m1_pre_topc(B_88,A_87)
      | v2_struct_0(B_88)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_2])).

tff(c_393,plain,(
    ! [A_73] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1(A_73,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(k8_tmap_1(A_73,'#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc('#skF_2',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_304,c_387])).

tff(c_407,plain,(
    ! [A_73] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1(A_73,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(k8_tmap_1(A_73,'#skF_2'))
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73)
      | ~ m1_pre_topc('#skF_2',A_73)
      | ~ l1_pre_topc(A_73) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_393])).

tff(c_440,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_419,c_407])).

tff(c_451,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_38,c_420,c_440])).

tff(c_452,plain,(
    v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_451])).

tff(c_204,plain,(
    ! [B_63,A_64] :
      ( v1_tsep_1(B_63,A_64)
      | ~ v3_pre_topc(u1_struct_0(B_63),A_64)
      | ~ m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_224,plain,(
    ! [B_25,A_23] :
      ( v1_tsep_1(B_25,A_23)
      | ~ v3_pre_topc(u1_struct_0(B_25),A_23)
      | ~ v2_pre_topc(A_23)
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_24,c_204])).

tff(c_468,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_452,c_224])).

tff(c_474,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_30,c_468])).

tff(c_475,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_474])).

tff(c_478,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_475])).

tff(c_481,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_478])).

tff(c_483,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.44  
% 2.67/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.45  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.45  
% 2.67/1.45  %Foreground sorts:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Background operators:
% 2.67/1.45  
% 2.67/1.45  
% 2.67/1.45  %Foreground operators:
% 2.67/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.67/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.67/1.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.67/1.45  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 2.67/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.67/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.45  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.67/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.67/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.67/1.45  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.67/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.67/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.45  
% 3.08/1.46  tff(f_131, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_pre_topc(C, k8_tmap_1(A, B)) => ((u1_struct_0(C) = u1_struct_0(B)) => (v1_tsep_1(C, k8_tmap_1(A, B)) & m1_pre_topc(C, k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 3.08/1.46  tff(f_49, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 3.08/1.46  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 3.08/1.46  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.08/1.46  tff(f_61, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 3.08/1.46  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.08/1.46  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.08/1.46  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_8, plain, (![A_4, B_5]: (v2_pre_topc(k8_tmap_1(A_4, B_5)) | ~m1_pre_topc(B_5, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.46  tff(c_30, plain, (m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_26, plain, (~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_42, plain, (~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 3.08/1.46  tff(c_6, plain, (![A_4, B_5]: (l1_pre_topc(k8_tmap_1(A_4, B_5)) | ~m1_pre_topc(B_5, A_4) | ~l1_pre_topc(A_4) | ~v2_pre_topc(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.08/1.46  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_134, plain, (![A_53, B_54]: (u1_struct_0(k8_tmap_1(A_53, B_54))=u1_struct_0(A_53) | ~m1_pre_topc(B_54, A_53) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.08/1.46  tff(c_24, plain, (![B_25, A_23]: (m1_subset_1(u1_struct_0(B_25), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.46  tff(c_380, plain, (![B_83, A_84, B_85]: (m1_subset_1(u1_struct_0(B_83), k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_pre_topc(B_83, k8_tmap_1(A_84, B_85)) | ~l1_pre_topc(k8_tmap_1(A_84, B_85)) | ~m1_pre_topc(B_85, A_84) | v2_struct_0(B_85) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(superposition, [status(thm), theory('equality')], [c_134, c_24])).
% 3.08/1.46  tff(c_382, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_380])).
% 3.08/1.46  tff(c_385, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_382])).
% 3.08/1.46  tff(c_386, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_34, c_385])).
% 3.08/1.46  tff(c_410, plain, (~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_386])).
% 3.08/1.46  tff(c_413, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_410])).
% 3.08/1.46  tff(c_416, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_413])).
% 3.08/1.46  tff(c_418, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_416])).
% 3.08/1.46  tff(c_420, plain, (l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_386])).
% 3.08/1.46  tff(c_419, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_386])).
% 3.08/1.46  tff(c_28, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.08/1.46  tff(c_47, plain, (![B_30, A_31]: (m1_subset_1(u1_struct_0(B_30), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_30, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.08/1.46  tff(c_50, plain, (![A_31]: (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc('#skF_2', A_31) | ~l1_pre_topc(A_31))), inference(superposition, [status(thm), theory('equality')], [c_28, c_47])).
% 3.08/1.46  tff(c_226, plain, (![A_65, B_66]: (k5_tmap_1(A_65, u1_struct_0(B_66))=u1_pre_topc(k8_tmap_1(A_65, B_66)) | ~m1_subset_1(u1_struct_0(B_66), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_pre_topc(B_66, A_65) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.08/1.46  tff(c_241, plain, (![A_65]: (k5_tmap_1(A_65, u1_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1(A_65, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_pre_topc('#skF_2', A_65) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(superposition, [status(thm), theory('equality')], [c_28, c_226])).
% 3.08/1.46  tff(c_247, plain, (![A_65]: (k5_tmap_1(A_65, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_65, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_65))) | ~m1_pre_topc('#skF_2', A_65) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_241])).
% 3.08/1.46  tff(c_276, plain, (![A_71]: (k5_tmap_1(A_71, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_71, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_pre_topc('#skF_2', A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(negUnitSimplification, [status(thm)], [c_34, c_247])).
% 3.08/1.46  tff(c_298, plain, (![A_73]: (k5_tmap_1(A_73, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_73, '#skF_2')) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc('#skF_2', A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_50, c_276])).
% 3.08/1.46  tff(c_115, plain, (![B_49, A_50]: (r2_hidden(B_49, k5_tmap_1(A_50, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.08/1.46  tff(c_122, plain, (![A_31]: (r2_hidden(u1_struct_0('#skF_3'), k5_tmap_1(A_31, u1_struct_0('#skF_3'))) | ~v2_pre_topc(A_31) | v2_struct_0(A_31) | ~m1_pre_topc('#skF_2', A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_50, c_115])).
% 3.08/1.46  tff(c_304, plain, (![A_73]: (r2_hidden(u1_struct_0('#skF_3'), u1_pre_topc(k8_tmap_1(A_73, '#skF_2'))) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc('#skF_2', A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc('#skF_2', A_73) | ~l1_pre_topc(A_73))), inference(superposition, [status(thm), theory('equality')], [c_298, c_122])).
% 3.08/1.46  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.08/1.46  tff(c_387, plain, (![B_86, A_87, B_88]: (v3_pre_topc(B_86, k8_tmap_1(A_87, B_88)) | ~r2_hidden(B_86, u1_pre_topc(k8_tmap_1(A_87, B_88))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(k8_tmap_1(A_87, B_88)) | ~m1_pre_topc(B_88, A_87) | v2_struct_0(B_88) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(superposition, [status(thm), theory('equality')], [c_134, c_2])).
% 3.08/1.46  tff(c_393, plain, (![A_73]: (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1(A_73, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(k8_tmap_1(A_73, '#skF_2')) | v2_struct_0('#skF_2') | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc('#skF_2', A_73) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_304, c_387])).
% 3.08/1.46  tff(c_407, plain, (![A_73]: (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1(A_73, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(k8_tmap_1(A_73, '#skF_2')) | ~v2_pre_topc(A_73) | v2_struct_0(A_73) | ~m1_pre_topc('#skF_2', A_73) | ~l1_pre_topc(A_73))), inference(negUnitSimplification, [status(thm)], [c_34, c_393])).
% 3.08/1.46  tff(c_440, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_419, c_407])).
% 3.08/1.46  tff(c_451, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_38, c_420, c_440])).
% 3.08/1.46  tff(c_452, plain, (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_451])).
% 3.08/1.46  tff(c_204, plain, (![B_63, A_64]: (v1_tsep_1(B_63, A_64) | ~v3_pre_topc(u1_struct_0(B_63), A_64) | ~m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.08/1.46  tff(c_224, plain, (![B_25, A_23]: (v1_tsep_1(B_25, A_23) | ~v3_pre_topc(u1_struct_0(B_25), A_23) | ~v2_pre_topc(A_23) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_24, c_204])).
% 3.08/1.46  tff(c_468, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_452, c_224])).
% 3.08/1.46  tff(c_474, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_420, c_30, c_468])).
% 3.08/1.46  tff(c_475, plain, (~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_474])).
% 3.08/1.46  tff(c_478, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_475])).
% 3.08/1.46  tff(c_481, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_478])).
% 3.08/1.46  tff(c_483, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_481])).
% 3.08/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.46  
% 3.08/1.46  Inference rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Ref     : 0
% 3.08/1.46  #Sup     : 102
% 3.08/1.46  #Fact    : 0
% 3.08/1.46  #Define  : 0
% 3.08/1.46  #Split   : 2
% 3.08/1.46  #Chain   : 0
% 3.08/1.46  #Close   : 0
% 3.08/1.46  
% 3.08/1.46  Ordering : KBO
% 3.08/1.46  
% 3.08/1.46  Simplification rules
% 3.08/1.46  ----------------------
% 3.08/1.46  #Subsume      : 27
% 3.08/1.46  #Demod        : 28
% 3.08/1.46  #Tautology    : 18
% 3.08/1.46  #SimpNegUnit  : 14
% 3.08/1.46  #BackRed      : 0
% 3.08/1.46  
% 3.08/1.46  #Partial instantiations: 0
% 3.08/1.46  #Strategies tried      : 1
% 3.08/1.46  
% 3.08/1.46  Timing (in seconds)
% 3.08/1.46  ----------------------
% 3.08/1.47  Preprocessing        : 0.34
% 3.08/1.47  Parsing              : 0.18
% 3.08/1.47  CNF conversion       : 0.02
% 3.08/1.47  Main loop            : 0.31
% 3.08/1.47  Inferencing          : 0.12
% 3.08/1.47  Reduction            : 0.09
% 3.08/1.47  Demodulation         : 0.06
% 3.08/1.47  BG Simplification    : 0.02
% 3.08/1.47  Subsumption          : 0.07
% 3.08/1.47  Abstraction          : 0.01
% 3.08/1.47  MUC search           : 0.00
% 3.08/1.47  Cooper               : 0.00
% 3.08/1.47  Total                : 0.69
% 3.08/1.47  Index Insertion      : 0.00
% 3.08/1.47  Index Deletion       : 0.00
% 3.08/1.47  Index Matching       : 0.00
% 3.08/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
