%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 148 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 478 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_111,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_168,plain,(
    ! [B_51,A_52] :
      ( l1_pre_topc(B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_171,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_180,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_4,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_174,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_168])).

tff(c_183,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_174])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_40,plain,(
    ! [B_26,A_27] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_43,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_43])).

tff(c_20,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_60,plain,(
    ! [B_30,A_31] :
      ( r1_tsep_1(B_30,A_31)
      | ~ r1_tsep_1(A_31,B_30)
      | ~ l1_struct_0(B_30)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_60])).

tff(c_64,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_67,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_67])).

tff(c_73,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_46,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_40])).

tff(c_55,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46])).

tff(c_72,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_74,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_77,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_81,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_77])).

tff(c_83,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_100,plain,(
    ! [B_38,C_39,A_40] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0(C_39))
      | ~ m1_pre_topc(B_38,C_39)
      | ~ m1_pre_topc(C_39,A_40)
      | ~ m1_pre_topc(B_38,A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_104,plain,(
    ! [B_38] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_38,'#skF_3')
      | ~ m1_pre_topc(B_38,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_123,plain,(
    ! [B_42] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_42,'#skF_3')
      | ~ m1_pre_topc(B_42,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_104])).

tff(c_90,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(u1_struct_0(A_34),u1_struct_0(B_35))
      | ~ r1_tsep_1(A_34,B_35)
      | ~ l1_struct_0(B_35)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(u1_struct_0(A_34),u1_struct_0(B_35))
      | v1_xboole_0(u1_struct_0(A_34))
      | ~ r1_tsep_1(A_34,B_35)
      | ~ l1_struct_0(B_35)
      | ~ l1_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_126,plain,(
    ! [B_42] :
      ( v1_xboole_0(u1_struct_0(B_42))
      | ~ r1_tsep_1(B_42,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(B_42)
      | ~ m1_pre_topc(B_42,'#skF_3')
      | ~ m1_pre_topc(B_42,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_123,c_98])).

tff(c_151,plain,(
    ! [B_48] :
      ( v1_xboole_0(u1_struct_0(B_48))
      | ~ r1_tsep_1(B_48,'#skF_3')
      | ~ l1_struct_0(B_48)
      | ~ m1_pre_topc(B_48,'#skF_3')
      | ~ m1_pre_topc(B_48,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_126])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_156,plain,(
    ! [B_49] :
      ( v2_struct_0(B_49)
      | ~ r1_tsep_1(B_49,'#skF_3')
      | ~ l1_struct_0(B_49)
      | ~ m1_pre_topc(B_49,'#skF_3')
      | ~ m1_pre_topc(B_49,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_159,plain,
    ( v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_156])).

tff(c_162,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_73,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_162])).

tff(c_166,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_165,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_188,plain,(
    ! [B_55,A_56] :
      ( r1_tsep_1(B_55,A_56)
      | ~ r1_tsep_1(A_56,B_55)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_190,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_165,c_188])).

tff(c_193,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_190])).

tff(c_194,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_197,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_197])).

tff(c_202,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.33  
% 2.30/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.33  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.33  
% 2.30/1.33  %Foreground sorts:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Background operators:
% 2.30/1.33  
% 2.30/1.33  
% 2.30/1.33  %Foreground operators:
% 2.30/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.30/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.30/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.30/1.33  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.30/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.33  
% 2.30/1.35  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.30/1.35  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.30/1.35  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.30/1.35  tff(f_69, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.30/1.35  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.30/1.35  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.30/1.35  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.30/1.35  tff(f_52, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.30/1.35  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_168, plain, (![B_51, A_52]: (l1_pre_topc(B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.35  tff(c_171, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_168])).
% 2.30/1.35  tff(c_180, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_171])).
% 2.30/1.35  tff(c_4, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.35  tff(c_24, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_174, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_168])).
% 2.30/1.35  tff(c_183, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_174])).
% 2.30/1.35  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_40, plain, (![B_26, A_27]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.35  tff(c_43, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.30/1.35  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_43])).
% 2.30/1.35  tff(c_20, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_38, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 2.30/1.35  tff(c_60, plain, (![B_30, A_31]: (r1_tsep_1(B_30, A_31) | ~r1_tsep_1(A_31, B_30) | ~l1_struct_0(B_30) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.30/1.35  tff(c_63, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_60])).
% 2.30/1.35  tff(c_64, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_63])).
% 2.30/1.35  tff(c_67, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_64])).
% 2.30/1.35  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_67])).
% 2.30/1.35  tff(c_73, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_63])).
% 2.30/1.35  tff(c_46, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_40])).
% 2.30/1.35  tff(c_55, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46])).
% 2.30/1.35  tff(c_72, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_63])).
% 2.30/1.35  tff(c_74, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 2.30/1.35  tff(c_77, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.30/1.35  tff(c_81, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_77])).
% 2.30/1.35  tff(c_83, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 2.30/1.35  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.30/1.35  tff(c_100, plain, (![B_38, C_39, A_40]: (r1_tarski(u1_struct_0(B_38), u1_struct_0(C_39)) | ~m1_pre_topc(B_38, C_39) | ~m1_pre_topc(C_39, A_40) | ~m1_pre_topc(B_38, A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.30/1.35  tff(c_104, plain, (![B_38]: (r1_tarski(u1_struct_0(B_38), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_38, '#skF_3') | ~m1_pre_topc(B_38, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.30/1.35  tff(c_123, plain, (![B_42]: (r1_tarski(u1_struct_0(B_42), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_42, '#skF_3') | ~m1_pre_topc(B_42, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_104])).
% 2.30/1.35  tff(c_90, plain, (![A_34, B_35]: (r1_xboole_0(u1_struct_0(A_34), u1_struct_0(B_35)) | ~r1_tsep_1(A_34, B_35) | ~l1_struct_0(B_35) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.35  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.35  tff(c_98, plain, (![A_34, B_35]: (~r1_tarski(u1_struct_0(A_34), u1_struct_0(B_35)) | v1_xboole_0(u1_struct_0(A_34)) | ~r1_tsep_1(A_34, B_35) | ~l1_struct_0(B_35) | ~l1_struct_0(A_34))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.30/1.35  tff(c_126, plain, (![B_42]: (v1_xboole_0(u1_struct_0(B_42)) | ~r1_tsep_1(B_42, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(B_42) | ~m1_pre_topc(B_42, '#skF_3') | ~m1_pre_topc(B_42, '#skF_1'))), inference(resolution, [status(thm)], [c_123, c_98])).
% 2.30/1.35  tff(c_151, plain, (![B_48]: (v1_xboole_0(u1_struct_0(B_48)) | ~r1_tsep_1(B_48, '#skF_3') | ~l1_struct_0(B_48) | ~m1_pre_topc(B_48, '#skF_3') | ~m1_pre_topc(B_48, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_126])).
% 2.30/1.35  tff(c_8, plain, (![A_7]: (~v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.35  tff(c_156, plain, (![B_49]: (v2_struct_0(B_49) | ~r1_tsep_1(B_49, '#skF_3') | ~l1_struct_0(B_49) | ~m1_pre_topc(B_49, '#skF_3') | ~m1_pre_topc(B_49, '#skF_1'))), inference(resolution, [status(thm)], [c_151, c_8])).
% 2.30/1.35  tff(c_159, plain, (v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_156])).
% 2.30/1.35  tff(c_162, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_73, c_159])).
% 2.30/1.35  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_162])).
% 2.30/1.35  tff(c_166, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.30/1.35  tff(c_165, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 2.30/1.35  tff(c_188, plain, (![B_55, A_56]: (r1_tsep_1(B_55, A_56) | ~r1_tsep_1(A_56, B_55) | ~l1_struct_0(B_55) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.30/1.35  tff(c_190, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_165, c_188])).
% 2.30/1.35  tff(c_193, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_166, c_190])).
% 2.30/1.35  tff(c_194, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_193])).
% 2.30/1.35  tff(c_197, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_194])).
% 2.30/1.35  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_183, c_197])).
% 2.30/1.35  tff(c_202, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_193])).
% 2.30/1.35  tff(c_206, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_202])).
% 2.30/1.35  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_206])).
% 2.30/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.35  
% 2.30/1.35  Inference rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Ref     : 0
% 2.30/1.35  #Sup     : 26
% 2.30/1.35  #Fact    : 0
% 2.30/1.35  #Define  : 0
% 2.30/1.35  #Split   : 5
% 2.30/1.35  #Chain   : 0
% 2.30/1.35  #Close   : 0
% 2.30/1.35  
% 2.30/1.35  Ordering : KBO
% 2.30/1.35  
% 2.30/1.35  Simplification rules
% 2.30/1.35  ----------------------
% 2.30/1.35  #Subsume      : 0
% 2.30/1.35  #Demod        : 27
% 2.30/1.35  #Tautology    : 6
% 2.30/1.35  #SimpNegUnit  : 3
% 2.30/1.35  #BackRed      : 0
% 2.30/1.35  
% 2.30/1.35  #Partial instantiations: 0
% 2.30/1.35  #Strategies tried      : 1
% 2.30/1.35  
% 2.30/1.35  Timing (in seconds)
% 2.30/1.35  ----------------------
% 2.30/1.35  Preprocessing        : 0.31
% 2.30/1.35  Parsing              : 0.18
% 2.30/1.35  CNF conversion       : 0.02
% 2.30/1.35  Main loop            : 0.20
% 2.30/1.35  Inferencing          : 0.08
% 2.30/1.35  Reduction            : 0.05
% 2.30/1.35  Demodulation         : 0.04
% 2.30/1.35  BG Simplification    : 0.02
% 2.30/1.35  Subsumption          : 0.03
% 2.30/1.35  Abstraction          : 0.01
% 2.30/1.35  MUC search           : 0.00
% 2.30/1.36  Cooper               : 0.00
% 2.30/1.36  Total                : 0.54
% 2.30/1.36  Index Insertion      : 0.00
% 2.30/1.36  Index Deletion       : 0.00
% 2.30/1.36  Index Matching       : 0.00
% 2.30/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
