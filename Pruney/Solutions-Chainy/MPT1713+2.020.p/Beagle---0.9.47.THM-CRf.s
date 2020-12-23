%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 165 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 484 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_281,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_287,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_281])).

tff(c_294,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_287])).

tff(c_16,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_290,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_281])).

tff(c_297,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_290])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    ! [B_34,A_35] :
      ( l1_pre_topc(B_34)
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_71,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_30,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_47,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_86,plain,(
    ! [B_40,A_41] :
      ( r1_tsep_1(B_40,A_41)
      | ~ r1_tsep_1(A_41,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_86])).

tff(c_90,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_98,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_90])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_98])).

tff(c_104,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_67])).

tff(c_103,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_105,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_108,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_108])).

tff(c_114,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_144,plain,(
    ! [A_52,B_53] :
      ( r1_xboole_0(u1_struct_0(A_52),u1_struct_0(B_53))
      | ~ r1_tsep_1(A_52,B_53)
      | ~ l1_struct_0(B_53)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(u1_struct_0(A_56),u1_struct_0(B_57)) = u1_struct_0(A_56)
      | ~ r1_tsep_1(A_56,B_57)
      | ~ l1_struct_0(B_57)
      | ~ l1_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_120,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(u1_struct_0(B_46),u1_struct_0(A_47))
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_120,c_12])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_129,plain,(
    ! [B_46,A_47] :
      ( k4_xboole_0(u1_struct_0(B_46),u1_struct_0(A_47)) = k1_xboole_0
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_125,c_6])).

tff(c_180,plain,(
    ! [A_60,B_61] :
      ( u1_struct_0(A_60) = k1_xboole_0
      | ~ m1_pre_topc(A_60,B_61)
      | ~ l1_pre_topc(B_61)
      | ~ r1_tsep_1(A_60,B_61)
      | ~ l1_struct_0(B_61)
      | ~ l1_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_129])).

tff(c_189,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_180])).

tff(c_196,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_114,c_74,c_32,c_189])).

tff(c_20,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_20])).

tff(c_268,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2,c_242])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_268])).

tff(c_272,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_271,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_317,plain,(
    ! [B_78,A_79] :
      ( r1_tsep_1(B_78,A_79)
      | ~ r1_tsep_1(A_79,B_78)
      | ~ l1_struct_0(B_78)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_319,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_271,c_317])).

tff(c_322,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_319])).

tff(c_323,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_326,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_323])).

tff(c_330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_326])).

tff(c_331,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_335,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_331])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.35  
% 2.34/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.35  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.34/1.35  
% 2.34/1.35  %Foreground sorts:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Background operators:
% 2.34/1.35  
% 2.34/1.35  
% 2.34/1.35  %Foreground operators:
% 2.34/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.35  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.34/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.35  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.34/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.35  
% 2.56/1.37  tff(f_109, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.56/1.37  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.56/1.37  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.56/1.37  tff(f_74, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.56/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.37  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.56/1.37  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.56/1.37  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.56/1.37  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.37  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.56/1.37  tff(f_57, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.56/1.37  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_281, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.37  tff(c_287, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_281])).
% 2.56/1.37  tff(c_294, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_287])).
% 2.56/1.37  tff(c_16, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.56/1.37  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_290, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_281])).
% 2.56/1.37  tff(c_297, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_290])).
% 2.56/1.37  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_58, plain, (![B_34, A_35]: (l1_pre_topc(B_34) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.37  tff(c_64, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.56/1.37  tff(c_71, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 2.56/1.37  tff(c_30, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_47, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.56/1.37  tff(c_86, plain, (![B_40, A_41]: (r1_tsep_1(B_40, A_41) | ~r1_tsep_1(A_41, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.37  tff(c_89, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_47, c_86])).
% 2.56/1.37  tff(c_90, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_89])).
% 2.56/1.37  tff(c_98, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_90])).
% 2.56/1.37  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_98])).
% 2.56/1.37  tff(c_104, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_89])).
% 2.56/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.56/1.37  tff(c_67, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.56/1.37  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_67])).
% 2.56/1.37  tff(c_103, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_89])).
% 2.56/1.37  tff(c_105, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_103])).
% 2.56/1.37  tff(c_108, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_105])).
% 2.56/1.37  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_108])).
% 2.56/1.37  tff(c_114, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_103])).
% 2.56/1.37  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.56/1.37  tff(c_144, plain, (![A_52, B_53]: (r1_xboole_0(u1_struct_0(A_52), u1_struct_0(B_53)) | ~r1_tsep_1(A_52, B_53) | ~l1_struct_0(B_53) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.56/1.37  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.56/1.37  tff(c_157, plain, (![A_56, B_57]: (k4_xboole_0(u1_struct_0(A_56), u1_struct_0(B_57))=u1_struct_0(A_56) | ~r1_tsep_1(A_56, B_57) | ~l1_struct_0(B_57) | ~l1_struct_0(A_56))), inference(resolution, [status(thm)], [c_144, c_8])).
% 2.56/1.37  tff(c_120, plain, (![B_44, A_45]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.56/1.37  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.37  tff(c_125, plain, (![B_46, A_47]: (r1_tarski(u1_struct_0(B_46), u1_struct_0(A_47)) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_120, c_12])).
% 2.56/1.37  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.56/1.37  tff(c_129, plain, (![B_46, A_47]: (k4_xboole_0(u1_struct_0(B_46), u1_struct_0(A_47))=k1_xboole_0 | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_125, c_6])).
% 2.56/1.37  tff(c_180, plain, (![A_60, B_61]: (u1_struct_0(A_60)=k1_xboole_0 | ~m1_pre_topc(A_60, B_61) | ~l1_pre_topc(B_61) | ~r1_tsep_1(A_60, B_61) | ~l1_struct_0(B_61) | ~l1_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_157, c_129])).
% 2.56/1.37  tff(c_189, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_47, c_180])).
% 2.56/1.37  tff(c_196, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_114, c_74, c_32, c_189])).
% 2.56/1.37  tff(c_20, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.37  tff(c_242, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_196, c_20])).
% 2.56/1.37  tff(c_268, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2, c_242])).
% 2.56/1.37  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_268])).
% 2.56/1.37  tff(c_272, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.56/1.37  tff(c_271, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.56/1.37  tff(c_317, plain, (![B_78, A_79]: (r1_tsep_1(B_78, A_79) | ~r1_tsep_1(A_79, B_78) | ~l1_struct_0(B_78) | ~l1_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.56/1.37  tff(c_319, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_271, c_317])).
% 2.56/1.37  tff(c_322, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_272, c_319])).
% 2.56/1.37  tff(c_323, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_322])).
% 2.56/1.37  tff(c_326, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_323])).
% 2.56/1.37  tff(c_330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_297, c_326])).
% 2.56/1.37  tff(c_331, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_322])).
% 2.56/1.37  tff(c_335, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_331])).
% 2.56/1.37  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_294, c_335])).
% 2.56/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  Inference rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Ref     : 0
% 2.56/1.37  #Sup     : 54
% 2.56/1.37  #Fact    : 0
% 2.56/1.37  #Define  : 0
% 2.56/1.37  #Split   : 5
% 2.56/1.37  #Chain   : 0
% 2.56/1.37  #Close   : 0
% 2.56/1.37  
% 2.56/1.37  Ordering : KBO
% 2.56/1.37  
% 2.56/1.37  Simplification rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Subsume      : 0
% 2.56/1.37  #Demod        : 37
% 2.56/1.37  #Tautology    : 18
% 2.56/1.37  #SimpNegUnit  : 2
% 2.56/1.37  #BackRed      : 0
% 2.56/1.37  
% 2.56/1.37  #Partial instantiations: 0
% 2.56/1.37  #Strategies tried      : 1
% 2.56/1.37  
% 2.56/1.37  Timing (in seconds)
% 2.56/1.37  ----------------------
% 2.56/1.37  Preprocessing        : 0.30
% 2.56/1.37  Parsing              : 0.18
% 2.56/1.37  CNF conversion       : 0.02
% 2.56/1.37  Main loop            : 0.23
% 2.56/1.37  Inferencing          : 0.09
% 2.56/1.37  Reduction            : 0.06
% 2.56/1.37  Demodulation         : 0.04
% 2.56/1.37  BG Simplification    : 0.01
% 2.56/1.37  Subsumption          : 0.04
% 2.56/1.37  Abstraction          : 0.01
% 2.56/1.37  MUC search           : 0.00
% 2.56/1.37  Cooper               : 0.00
% 2.56/1.37  Total                : 0.57
% 2.56/1.37  Index Insertion      : 0.00
% 2.56/1.37  Index Deletion       : 0.00
% 2.56/1.37  Index Matching       : 0.00
% 2.56/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
