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
% DateTime   : Thu Dec  3 10:27:58 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 175 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :   17
%              Number of atoms          :  252 ( 751 expanded)
%              Number of equality atoms :   13 (  67 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_135,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_87,axiom,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_105,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( v2_pre_topc(k8_tmap_1(A_6,B_7))
      | ~ m1_pre_topc(B_7,A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_30,plain,
    ( ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    ~ v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( l1_pre_topc(k8_tmap_1(A_6,B_7))
      | ~ m1_pre_topc(B_7,A_6)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_105,plain,(
    ! [A_57,B_58] :
      ( u1_struct_0(k8_tmap_1(A_57,B_58)) = u1_struct_0(A_57)
      | ~ m1_pre_topc(B_58,A_57)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [B_27,A_25] :
      ( r1_tarski(u1_struct_0(B_27),u1_struct_0(A_25))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_362,plain,(
    ! [B_87,A_88,B_89] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0(A_88))
      | ~ m1_pre_topc(B_87,k8_tmap_1(A_88,B_89))
      | ~ l1_pre_topc(k8_tmap_1(A_88,B_89))
      | ~ m1_pre_topc(B_89,A_88)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_28])).

tff(c_364,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_362])).

tff(c_367,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_364])).

tff(c_368,plain,
    ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_367])).

tff(c_369,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_372,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_369])).

tff(c_375,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_375])).

tff(c_379,plain,(
    l1_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_378,plain,(
    r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_57,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(u1_struct_0(B_36),u1_struct_0(A_37))
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_60,plain,(
    ! [A_37] :
      ( r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_37))
      | ~ m1_pre_topc('#skF_2',A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_57])).

tff(c_244,plain,(
    ! [A_73,B_74] :
      ( k5_tmap_1(A_73,u1_struct_0(B_74)) = u1_pre_topc(k8_tmap_1(A_73,B_74))
      | ~ m1_subset_1(u1_struct_0(B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc(B_74,A_73)
      | v2_struct_0(B_74)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_256,plain,(
    ! [A_73] :
      ( k5_tmap_1(A_73,u1_struct_0('#skF_2')) = u1_pre_topc(k8_tmap_1(A_73,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc('#skF_2',A_73)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_244])).

tff(c_261,plain,(
    ! [A_73] :
      ( k5_tmap_1(A_73,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_73,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_pre_topc('#skF_2',A_73)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_256])).

tff(c_270,plain,(
    ! [A_77] :
      ( k5_tmap_1(A_77,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_77,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc('#skF_2',A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_261])).

tff(c_282,plain,(
    ! [A_78] :
      ( k5_tmap_1(A_78,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_78,'#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_270])).

tff(c_299,plain,(
    ! [A_79] :
      ( k5_tmap_1(A_79,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_79,'#skF_2'))
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ m1_pre_topc('#skF_2',A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_60,c_282])).

tff(c_96,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,k5_tmap_1(A_54,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    ! [A_1,A_54] :
      ( r2_hidden(A_1,k5_tmap_1(A_54,A_1))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54)
      | ~ r1_tarski(A_1,u1_struct_0(A_54)) ) ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_387,plain,(
    ! [A_95] :
      ( r2_hidden(u1_struct_0('#skF_3'),u1_pre_topc(k8_tmap_1(A_95,'#skF_2')))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_95))
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | ~ m1_pre_topc('#skF_2',A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_102])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v3_pre_topc(B_5,A_3)
      | ~ r2_hidden(B_5,u1_pre_topc(A_3))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [B_5,A_57,B_58] :
      ( v3_pre_topc(B_5,k8_tmap_1(A_57,B_58))
      | ~ r2_hidden(B_5,u1_pre_topc(k8_tmap_1(A_57,B_58)))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(k8_tmap_1(A_57,B_58))
      | ~ m1_pre_topc(B_58,A_57)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_6])).

tff(c_390,plain,(
    ! [A_95] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1(A_95,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(k8_tmap_1(A_95,'#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_95))
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95)
      | ~ m1_pre_topc('#skF_2',A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_387,c_116])).

tff(c_399,plain,(
    ! [A_96] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1(A_96,'#skF_2'))
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(k8_tmap_1(A_96,'#skF_2'))
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_96))
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96)
      | ~ m1_pre_topc('#skF_2',A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_390])).

tff(c_412,plain,(
    ! [A_97] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),k8_tmap_1(A_97,'#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1(A_97,'#skF_2'))
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97)
      | ~ m1_pre_topc('#skF_2',A_97)
      | ~ l1_pre_topc(A_97)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_97)) ) ),
    inference(resolution,[status(thm)],[c_4,c_399])).

tff(c_179,plain,(
    ! [B_66,A_67] :
      ( v1_tsep_1(B_66,A_67)
      | ~ v3_pre_topc(u1_struct_0(B_66),A_67)
      | ~ m1_subset_1(u1_struct_0(B_66),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_197,plain,(
    ! [B_68,A_69] :
      ( v1_tsep_1(B_68,A_69)
      | ~ v3_pre_topc(u1_struct_0(B_68),A_69)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | ~ r1_tarski(u1_struct_0(B_68),u1_struct_0(A_69)) ) ),
    inference(resolution,[status(thm)],[c_4,c_179])).

tff(c_217,plain,(
    ! [B_27,A_25] :
      ( v1_tsep_1(B_27,A_25)
      | ~ v3_pre_topc(u1_struct_0(B_27),A_25)
      | ~ v2_pre_topc(A_25)
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_548,plain,(
    ! [A_121] :
      ( v1_tsep_1('#skF_3',k8_tmap_1(A_121,'#skF_2'))
      | ~ v2_pre_topc(k8_tmap_1(A_121,'#skF_2'))
      | ~ m1_pre_topc('#skF_3',k8_tmap_1(A_121,'#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1(A_121,'#skF_2'))
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121)
      | ~ m1_pre_topc('#skF_2',A_121)
      | ~ l1_pre_topc(A_121)
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_412,c_217])).

tff(c_551,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_378,c_548])).

tff(c_567,plain,
    ( v1_tsep_1('#skF_3',k8_tmap_1('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_42,c_379,c_34,c_551])).

tff(c_568,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_46,c_567])).

tff(c_574,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_568])).

tff(c_577,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_574])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.21/1.50  
% 3.21/1.50  %Foreground sorts:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Background operators:
% 3.21/1.50  
% 3.21/1.50  
% 3.21/1.50  %Foreground operators:
% 3.21/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.50  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.21/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.50  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 3.21/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.21/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.50  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.21/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.21/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.50  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.21/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.50  
% 3.21/1.51  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_pre_topc(C, k8_tmap_1(A, B)) => ((u1_struct_0(C) = u1_struct_0(B)) => (v1_tsep_1(C, k8_tmap_1(A, B)) & m1_pre_topc(C, k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 3.21/1.51  tff(f_53, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 3.21/1.51  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 3.21/1.51  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.21/1.51  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.51  tff(f_65, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 3.21/1.51  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.21/1.51  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.21/1.51  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_12, plain, (![A_6, B_7]: (v2_pre_topc(k8_tmap_1(A_6, B_7)) | ~m1_pre_topc(B_7, A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.51  tff(c_34, plain, (m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_30, plain, (~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_46, plain, (~v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30])).
% 3.21/1.51  tff(c_10, plain, (![A_6, B_7]: (l1_pre_topc(k8_tmap_1(A_6, B_7)) | ~m1_pre_topc(B_7, A_6) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.21/1.51  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_105, plain, (![A_57, B_58]: (u1_struct_0(k8_tmap_1(A_57, B_58))=u1_struct_0(A_57) | ~m1_pre_topc(B_58, A_57) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.21/1.51  tff(c_28, plain, (![B_27, A_25]: (r1_tarski(u1_struct_0(B_27), u1_struct_0(A_25)) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.51  tff(c_362, plain, (![B_87, A_88, B_89]: (r1_tarski(u1_struct_0(B_87), u1_struct_0(A_88)) | ~m1_pre_topc(B_87, k8_tmap_1(A_88, B_89)) | ~l1_pre_topc(k8_tmap_1(A_88, B_89)) | ~m1_pre_topc(B_89, A_88) | v2_struct_0(B_89) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(superposition, [status(thm), theory('equality')], [c_105, c_28])).
% 3.21/1.51  tff(c_364, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_362])).
% 3.21/1.51  tff(c_367, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_364])).
% 3.21/1.51  tff(c_368, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_367])).
% 3.21/1.51  tff(c_369, plain, (~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_368])).
% 3.21/1.51  tff(c_372, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_369])).
% 3.21/1.51  tff(c_375, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_372])).
% 3.21/1.51  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_375])).
% 3.21/1.51  tff(c_379, plain, (l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_368])).
% 3.21/1.51  tff(c_378, plain, (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_368])).
% 3.21/1.51  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.51  tff(c_32, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.21/1.51  tff(c_57, plain, (![B_36, A_37]: (r1_tarski(u1_struct_0(B_36), u1_struct_0(A_37)) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.21/1.51  tff(c_60, plain, (![A_37]: (r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_37)) | ~m1_pre_topc('#skF_2', A_37) | ~l1_pre_topc(A_37))), inference(superposition, [status(thm), theory('equality')], [c_32, c_57])).
% 3.21/1.51  tff(c_244, plain, (![A_73, B_74]: (k5_tmap_1(A_73, u1_struct_0(B_74))=u1_pre_topc(k8_tmap_1(A_73, B_74)) | ~m1_subset_1(u1_struct_0(B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc(B_74, A_73) | v2_struct_0(B_74) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.21/1.51  tff(c_256, plain, (![A_73]: (k5_tmap_1(A_73, u1_struct_0('#skF_2'))=u1_pre_topc(k8_tmap_1(A_73, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc('#skF_2', A_73) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(superposition, [status(thm), theory('equality')], [c_32, c_244])).
% 3.21/1.51  tff(c_261, plain, (![A_73]: (k5_tmap_1(A_73, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_73, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_pre_topc('#skF_2', A_73) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_256])).
% 3.21/1.51  tff(c_270, plain, (![A_77]: (k5_tmap_1(A_77, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_77, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc('#skF_2', A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(negUnitSimplification, [status(thm)], [c_38, c_261])).
% 3.21/1.51  tff(c_282, plain, (![A_78]: (k5_tmap_1(A_78, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_78, '#skF_2')) | ~m1_pre_topc('#skF_2', A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_78)))), inference(resolution, [status(thm)], [c_4, c_270])).
% 3.21/1.51  tff(c_299, plain, (![A_79]: (k5_tmap_1(A_79, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_79, '#skF_2')) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~m1_pre_topc('#skF_2', A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_60, c_282])).
% 3.21/1.51  tff(c_96, plain, (![B_53, A_54]: (r2_hidden(B_53, k5_tmap_1(A_54, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.51  tff(c_102, plain, (![A_1, A_54]: (r2_hidden(A_1, k5_tmap_1(A_54, A_1)) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54) | ~r1_tarski(A_1, u1_struct_0(A_54)))), inference(resolution, [status(thm)], [c_4, c_96])).
% 3.21/1.51  tff(c_387, plain, (![A_95]: (r2_hidden(u1_struct_0('#skF_3'), u1_pre_topc(k8_tmap_1(A_95, '#skF_2'))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_95)) | ~v2_pre_topc(A_95) | v2_struct_0(A_95) | ~m1_pre_topc('#skF_2', A_95) | ~l1_pre_topc(A_95))), inference(superposition, [status(thm), theory('equality')], [c_299, c_102])).
% 3.21/1.51  tff(c_6, plain, (![B_5, A_3]: (v3_pre_topc(B_5, A_3) | ~r2_hidden(B_5, u1_pre_topc(A_3)) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.21/1.51  tff(c_116, plain, (![B_5, A_57, B_58]: (v3_pre_topc(B_5, k8_tmap_1(A_57, B_58)) | ~r2_hidden(B_5, u1_pre_topc(k8_tmap_1(A_57, B_58))) | ~m1_subset_1(B_5, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(k8_tmap_1(A_57, B_58)) | ~m1_pre_topc(B_58, A_57) | v2_struct_0(B_58) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_105, c_6])).
% 3.21/1.51  tff(c_390, plain, (![A_95]: (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1(A_95, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(k8_tmap_1(A_95, '#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_95)) | ~v2_pre_topc(A_95) | v2_struct_0(A_95) | ~m1_pre_topc('#skF_2', A_95) | ~l1_pre_topc(A_95))), inference(resolution, [status(thm)], [c_387, c_116])).
% 3.21/1.51  tff(c_399, plain, (![A_96]: (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1(A_96, '#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(k8_tmap_1(A_96, '#skF_2')) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_96)) | ~v2_pre_topc(A_96) | v2_struct_0(A_96) | ~m1_pre_topc('#skF_2', A_96) | ~l1_pre_topc(A_96))), inference(negUnitSimplification, [status(thm)], [c_38, c_390])).
% 3.21/1.51  tff(c_412, plain, (![A_97]: (v3_pre_topc(u1_struct_0('#skF_3'), k8_tmap_1(A_97, '#skF_2')) | ~l1_pre_topc(k8_tmap_1(A_97, '#skF_2')) | ~v2_pre_topc(A_97) | v2_struct_0(A_97) | ~m1_pre_topc('#skF_2', A_97) | ~l1_pre_topc(A_97) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_97)))), inference(resolution, [status(thm)], [c_4, c_399])).
% 3.21/1.51  tff(c_179, plain, (![B_66, A_67]: (v1_tsep_1(B_66, A_67) | ~v3_pre_topc(u1_struct_0(B_66), A_67) | ~m1_subset_1(u1_struct_0(B_66), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.21/1.51  tff(c_197, plain, (![B_68, A_69]: (v1_tsep_1(B_68, A_69) | ~v3_pre_topc(u1_struct_0(B_68), A_69) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | ~r1_tarski(u1_struct_0(B_68), u1_struct_0(A_69)))), inference(resolution, [status(thm)], [c_4, c_179])).
% 3.21/1.51  tff(c_217, plain, (![B_27, A_25]: (v1_tsep_1(B_27, A_25) | ~v3_pre_topc(u1_struct_0(B_27), A_25) | ~v2_pre_topc(A_25) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_28, c_197])).
% 3.21/1.51  tff(c_548, plain, (![A_121]: (v1_tsep_1('#skF_3', k8_tmap_1(A_121, '#skF_2')) | ~v2_pre_topc(k8_tmap_1(A_121, '#skF_2')) | ~m1_pre_topc('#skF_3', k8_tmap_1(A_121, '#skF_2')) | ~l1_pre_topc(k8_tmap_1(A_121, '#skF_2')) | ~v2_pre_topc(A_121) | v2_struct_0(A_121) | ~m1_pre_topc('#skF_2', A_121) | ~l1_pre_topc(A_121) | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_412, c_217])).
% 3.21/1.51  tff(c_551, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_378, c_548])).
% 3.21/1.51  tff(c_567, plain, (v1_tsep_1('#skF_3', k8_tmap_1('#skF_1', '#skF_2')) | ~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_42, c_379, c_34, c_551])).
% 3.21/1.51  tff(c_568, plain, (~v2_pre_topc(k8_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_46, c_567])).
% 3.21/1.51  tff(c_574, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_568])).
% 3.21/1.51  tff(c_577, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_574])).
% 3.21/1.51  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_577])).
% 3.21/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.51  
% 3.21/1.51  Inference rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Ref     : 0
% 3.21/1.51  #Sup     : 126
% 3.21/1.51  #Fact    : 0
% 3.21/1.51  #Define  : 0
% 3.21/1.51  #Split   : 4
% 3.21/1.51  #Chain   : 0
% 3.21/1.51  #Close   : 0
% 3.21/1.51  
% 3.21/1.51  Ordering : KBO
% 3.21/1.51  
% 3.21/1.51  Simplification rules
% 3.21/1.51  ----------------------
% 3.21/1.51  #Subsume      : 44
% 3.21/1.51  #Demod        : 35
% 3.21/1.51  #Tautology    : 21
% 3.21/1.51  #SimpNegUnit  : 22
% 3.21/1.51  #BackRed      : 0
% 3.21/1.51  
% 3.21/1.51  #Partial instantiations: 0
% 3.21/1.51  #Strategies tried      : 1
% 3.21/1.51  
% 3.21/1.51  Timing (in seconds)
% 3.21/1.51  ----------------------
% 3.21/1.52  Preprocessing        : 0.32
% 3.21/1.52  Parsing              : 0.17
% 3.21/1.52  CNF conversion       : 0.02
% 3.21/1.52  Main loop            : 0.37
% 3.21/1.52  Inferencing          : 0.14
% 3.21/1.52  Reduction            : 0.11
% 3.21/1.52  Demodulation         : 0.07
% 3.21/1.52  BG Simplification    : 0.02
% 3.21/1.52  Subsumption          : 0.09
% 3.21/1.52  Abstraction          : 0.02
% 3.21/1.52  MUC search           : 0.00
% 3.21/1.52  Cooper               : 0.00
% 3.21/1.52  Total                : 0.73
% 3.21/1.52  Index Insertion      : 0.00
% 3.21/1.52  Index Deletion       : 0.00
% 3.21/1.52  Index Matching       : 0.00
% 3.21/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
