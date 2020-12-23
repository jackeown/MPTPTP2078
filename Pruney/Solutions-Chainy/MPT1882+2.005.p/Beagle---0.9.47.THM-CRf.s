%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 257 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 985 expanded)
%              Number of equality atoms :    9 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_54,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_47,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_124,plain,(
    ! [A_44,B_45] :
      ( '#skF_1'(A_44,B_45) != B_45
      | v3_tex_2(B_45,A_44)
      | ~ v2_tex_2(B_45,A_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_131,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_124])).

tff(c_135,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_131])).

tff(c_136,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_135])).

tff(c_137,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_169,plain,(
    ! [B_54,A_55] :
      ( v2_tex_2(B_54,A_55)
      | ~ v1_zfmisc_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | v1_xboole_0(B_54)
      | ~ l1_pre_topc(A_55)
      | ~ v2_tdlat_3(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_176,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_169])).

tff(c_180,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_48,c_176])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_137,c_180])).

tff(c_184,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_204,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,'#skF_1'(A_61,B_60))
      | v3_tex_2(B_60,A_61)
      | ~ v2_tex_2(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_204])).

tff(c_213,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_184,c_209])).

tff(c_214,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_213])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [B_30,A_31] :
      ( v1_xboole_0(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(A_4)
      | ~ v1_xboole_0(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_220,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_214,c_66])).

tff(c_226,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_220])).

tff(c_183,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( B_18 = A_16
      | ~ r1_tarski(A_16,B_18)
      | ~ v1_zfmisc_1(B_18)
      | v1_xboole_0(B_18)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_217,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_214,c_20])).

tff(c_223,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_183,c_217])).

tff(c_227,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_223])).

tff(c_193,plain,(
    ! [A_58,B_59] :
      ( v2_tex_2('#skF_1'(A_58,B_59),A_58)
      | v3_tex_2(B_59,A_58)
      | ~ v2_tex_2(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_193])).

tff(c_202,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_184,c_198])).

tff(c_203,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_202])).

tff(c_278,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1('#skF_1'(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | v3_tex_2(B_75,A_74)
      | ~ v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [B_24,A_22] :
      ( v1_zfmisc_1(B_24)
      | ~ v2_tex_2(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | v1_xboole_0(B_24)
      | ~ l1_pre_topc(A_22)
      | ~ v2_tdlat_3(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_473,plain,(
    ! [A_101,B_102] :
      ( v1_zfmisc_1('#skF_1'(A_101,B_102))
      | ~ v2_tex_2('#skF_1'(A_101,B_102),A_101)
      | v1_xboole_0('#skF_1'(A_101,B_102))
      | ~ v2_tdlat_3(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101)
      | v3_tex_2(B_102,A_101)
      | ~ v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_278,c_26])).

tff(c_479,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_203,c_473])).

tff(c_484,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_184,c_36,c_34,c_479])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_38,c_226,c_227,c_484])).

tff(c_487,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_488,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_526,plain,(
    ! [B_113,A_114] :
      ( v2_tex_2(B_113,A_114)
      | ~ v3_tex_2(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_533,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_526])).

tff(c_537,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_488,c_533])).

tff(c_692,plain,(
    ! [B_141,A_142] :
      ( v1_zfmisc_1(B_141)
      | ~ v2_tex_2(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | v1_xboole_0(B_141)
      | ~ l1_pre_topc(A_142)
      | ~ v2_tdlat_3(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_702,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_692])).

tff(c_707,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_537,c_702])).

tff(c_709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_30,c_487,c_707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  
% 3.05/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.46  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.05/1.46  
% 3.05/1.46  %Foreground sorts:
% 3.05/1.46  
% 3.05/1.46  
% 3.05/1.46  %Background operators:
% 3.05/1.46  
% 3.05/1.46  
% 3.05/1.46  %Foreground operators:
% 3.05/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.05/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.05/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.46  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.05/1.46  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.05/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.05/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.05/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.05/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.46  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.05/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.05/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.05/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.05/1.46  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.05/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.05/1.46  
% 3.05/1.47  tff(f_120, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 3.05/1.47  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 3.05/1.47  tff(f_100, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 3.05/1.47  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.47  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.05/1.47  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.05/1.47  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_40, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_47, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 3.05/1.47  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_124, plain, (![A_44, B_45]: ('#skF_1'(A_44, B_45)!=B_45 | v3_tex_2(B_45, A_44) | ~v2_tex_2(B_45, A_44) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.47  tff(c_131, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_124])).
% 3.05/1.47  tff(c_135, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_131])).
% 3.05/1.47  tff(c_136, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_135])).
% 3.05/1.47  tff(c_137, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_136])).
% 3.05/1.47  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_34, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_46, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.05/1.47  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_47, c_46])).
% 3.05/1.47  tff(c_169, plain, (![B_54, A_55]: (v2_tex_2(B_54, A_55) | ~v1_zfmisc_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | v1_xboole_0(B_54) | ~l1_pre_topc(A_55) | ~v2_tdlat_3(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.05/1.47  tff(c_176, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_169])).
% 3.05/1.47  tff(c_180, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_48, c_176])).
% 3.05/1.47  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_137, c_180])).
% 3.05/1.47  tff(c_184, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_136])).
% 3.05/1.47  tff(c_204, plain, (![B_60, A_61]: (r1_tarski(B_60, '#skF_1'(A_61, B_60)) | v3_tex_2(B_60, A_61) | ~v2_tex_2(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.47  tff(c_209, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_204])).
% 3.05/1.47  tff(c_213, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_184, c_209])).
% 3.05/1.47  tff(c_214, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_47, c_213])).
% 3.05/1.47  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.05/1.47  tff(c_59, plain, (![B_30, A_31]: (v1_xboole_0(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.05/1.47  tff(c_66, plain, (![A_4, B_5]: (v1_xboole_0(A_4) | ~v1_xboole_0(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.05/1.47  tff(c_220, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_214, c_66])).
% 3.05/1.47  tff(c_226, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_220])).
% 3.05/1.47  tff(c_183, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_136])).
% 3.05/1.47  tff(c_20, plain, (![B_18, A_16]: (B_18=A_16 | ~r1_tarski(A_16, B_18) | ~v1_zfmisc_1(B_18) | v1_xboole_0(B_18) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.05/1.47  tff(c_217, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_214, c_20])).
% 3.05/1.47  tff(c_223, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_183, c_217])).
% 3.05/1.47  tff(c_227, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_226, c_223])).
% 3.05/1.47  tff(c_193, plain, (![A_58, B_59]: (v2_tex_2('#skF_1'(A_58, B_59), A_58) | v3_tex_2(B_59, A_58) | ~v2_tex_2(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.47  tff(c_198, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_193])).
% 3.05/1.47  tff(c_202, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_184, c_198])).
% 3.05/1.47  tff(c_203, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_47, c_202])).
% 3.05/1.47  tff(c_278, plain, (![A_74, B_75]: (m1_subset_1('#skF_1'(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | v3_tex_2(B_75, A_74) | ~v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.47  tff(c_26, plain, (![B_24, A_22]: (v1_zfmisc_1(B_24) | ~v2_tex_2(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | v1_xboole_0(B_24) | ~l1_pre_topc(A_22) | ~v2_tdlat_3(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.05/1.47  tff(c_473, plain, (![A_101, B_102]: (v1_zfmisc_1('#skF_1'(A_101, B_102)) | ~v2_tex_2('#skF_1'(A_101, B_102), A_101) | v1_xboole_0('#skF_1'(A_101, B_102)) | ~v2_tdlat_3(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101) | v3_tex_2(B_102, A_101) | ~v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_278, c_26])).
% 3.05/1.47  tff(c_479, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_203, c_473])).
% 3.05/1.47  tff(c_484, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_184, c_36, c_34, c_479])).
% 3.05/1.47  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_38, c_226, c_227, c_484])).
% 3.05/1.47  tff(c_487, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.05/1.47  tff(c_488, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.05/1.47  tff(c_526, plain, (![B_113, A_114]: (v2_tex_2(B_113, A_114) | ~v3_tex_2(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.47  tff(c_533, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_526])).
% 3.05/1.47  tff(c_537, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_488, c_533])).
% 3.05/1.47  tff(c_692, plain, (![B_141, A_142]: (v1_zfmisc_1(B_141) | ~v2_tex_2(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | v1_xboole_0(B_141) | ~l1_pre_topc(A_142) | ~v2_tdlat_3(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.05/1.47  tff(c_702, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_692])).
% 3.05/1.47  tff(c_707, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_537, c_702])).
% 3.05/1.47  tff(c_709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_30, c_487, c_707])).
% 3.05/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.47  
% 3.05/1.47  Inference rules
% 3.05/1.47  ----------------------
% 3.05/1.47  #Ref     : 0
% 3.05/1.47  #Sup     : 119
% 3.05/1.47  #Fact    : 0
% 3.05/1.47  #Define  : 0
% 3.05/1.47  #Split   : 6
% 3.05/1.47  #Chain   : 0
% 3.05/1.47  #Close   : 0
% 3.05/1.47  
% 3.05/1.47  Ordering : KBO
% 3.05/1.47  
% 3.05/1.47  Simplification rules
% 3.05/1.47  ----------------------
% 3.05/1.47  #Subsume      : 34
% 3.05/1.47  #Demod        : 106
% 3.05/1.47  #Tautology    : 16
% 3.05/1.47  #SimpNegUnit  : 40
% 3.05/1.47  #BackRed      : 0
% 3.05/1.47  
% 3.05/1.47  #Partial instantiations: 0
% 3.05/1.47  #Strategies tried      : 1
% 3.05/1.47  
% 3.05/1.47  Timing (in seconds)
% 3.05/1.47  ----------------------
% 3.05/1.48  Preprocessing        : 0.31
% 3.05/1.48  Parsing              : 0.17
% 3.05/1.48  CNF conversion       : 0.02
% 3.05/1.48  Main loop            : 0.39
% 3.05/1.48  Inferencing          : 0.15
% 3.05/1.48  Reduction            : 0.10
% 3.05/1.48  Demodulation         : 0.06
% 3.05/1.48  BG Simplification    : 0.02
% 3.05/1.48  Subsumption          : 0.09
% 3.05/1.48  Abstraction          : 0.02
% 3.05/1.48  MUC search           : 0.00
% 3.05/1.48  Cooper               : 0.00
% 3.05/1.48  Total                : 0.74
% 3.05/1.48  Index Insertion      : 0.00
% 3.05/1.48  Index Deletion       : 0.00
% 3.05/1.48  Index Matching       : 0.00
% 3.05/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
