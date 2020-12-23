%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:31 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 158 expanded)
%              Number of leaves         :   30 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 ( 490 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_127,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_281,plain,(
    ! [B_79,A_80] :
      ( l1_pre_topc(B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_284,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_281])).

tff(c_293,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_284])).

tff(c_12,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_287,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_281])).

tff(c_296,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_287])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_53,plain,(
    ! [B_37,A_38] :
      ( l1_pre_topc(B_37)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_65,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56])).

tff(c_28,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_46,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_81,plain,(
    ! [B_47,A_48] :
      ( r1_tsep_1(B_47,A_48)
      | ~ r1_tsep_1(A_48,B_47)
      | ~ l1_struct_0(B_47)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_85,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_88,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_88])).

tff(c_94,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_59,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_68,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_93,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_104,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_107,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_107])).

tff(c_113,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( r1_xboole_0(u1_struct_0(A_17),u1_struct_0(B_19))
      | ~ r1_tsep_1(A_17,B_19)
      | ~ l1_struct_0(B_19)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_131,plain,(
    ! [B_60,C_61,A_62] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0(C_61))
      | ~ m1_pre_topc(B_60,C_61)
      | ~ m1_pre_topc(C_61,A_62)
      | ~ m1_pre_topc(B_60,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_135,plain,(
    ! [B_60] :
      ( r1_tarski(u1_struct_0(B_60),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_60,'#skF_5')
      | ~ m1_pre_topc(B_60,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_131])).

tff(c_155,plain,(
    ! [B_64] :
      ( r1_tarski(u1_struct_0(B_64),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_64,'#skF_5')
      | ~ m1_pre_topc(B_64,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_135])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_164,plain,(
    ! [B_65] :
      ( k3_xboole_0(u1_struct_0(B_65),u1_struct_0('#skF_5')) = u1_struct_0(B_65)
      | ~ m1_pre_topc(B_65,'#skF_5')
      | ~ m1_pre_topc(B_65,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_155,c_10])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,k3_xboole_0(A_42,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_42,B_43] :
      ( ~ r1_xboole_0(A_42,B_43)
      | v1_xboole_0(k3_xboole_0(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_213,plain,(
    ! [B_68] :
      ( ~ r1_xboole_0(u1_struct_0(B_68),u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0(B_68))
      | ~ m1_pre_topc(B_68,'#skF_5')
      | ~ m1_pre_topc(B_68,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_79])).

tff(c_220,plain,(
    ! [A_17] :
      ( v1_xboole_0(u1_struct_0(A_17))
      | ~ m1_pre_topc(A_17,'#skF_5')
      | ~ m1_pre_topc(A_17,'#skF_3')
      | ~ r1_tsep_1(A_17,'#skF_5')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_20,c_213])).

tff(c_255,plain,(
    ! [A_74] :
      ( v1_xboole_0(u1_struct_0(A_74))
      | ~ m1_pre_topc(A_74,'#skF_5')
      | ~ m1_pre_topc(A_74,'#skF_3')
      | ~ r1_tsep_1(A_74,'#skF_5')
      | ~ l1_struct_0(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_220])).

tff(c_16,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_264,plain,(
    ! [A_75] :
      ( v2_struct_0(A_75)
      | ~ m1_pre_topc(A_75,'#skF_5')
      | ~ m1_pre_topc(A_75,'#skF_3')
      | ~ r1_tsep_1(A_75,'#skF_5')
      | ~ l1_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_255,c_16])).

tff(c_267,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_264])).

tff(c_270,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_30,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_270])).

tff(c_274,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_273,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_309,plain,(
    ! [B_89,A_90] :
      ( r1_tsep_1(B_89,A_90)
      | ~ r1_tsep_1(A_90,B_89)
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_311,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_273,c_309])).

tff(c_314,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_311])).

tff(c_315,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_318,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_315])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_318])).

tff(c_323,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_327,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_323])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.61  
% 2.41/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.61  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.41/1.61  
% 2.41/1.61  %Foreground sorts:
% 2.41/1.61  
% 2.41/1.61  
% 2.41/1.61  %Background operators:
% 2.41/1.61  
% 2.41/1.61  
% 2.41/1.61  %Foreground operators:
% 2.41/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.61  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.41/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.61  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.41/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.41/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.61  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.41/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.61  
% 2.72/1.63  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.72/1.63  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.72/1.63  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.72/1.63  tff(f_85, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.72/1.63  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.72/1.63  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.72/1.63  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.72/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.72/1.63  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.72/1.63  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.72/1.63  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_281, plain, (![B_79, A_80]: (l1_pre_topc(B_79) | ~m1_pre_topc(B_79, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.63  tff(c_284, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_281])).
% 2.72/1.63  tff(c_293, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_284])).
% 2.72/1.63  tff(c_12, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.63  tff(c_32, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_287, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_281])).
% 2.72/1.63  tff(c_296, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_287])).
% 2.72/1.63  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_53, plain, (![B_37, A_38]: (l1_pre_topc(B_37) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.63  tff(c_56, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_53])).
% 2.72/1.63  tff(c_65, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56])).
% 2.72/1.63  tff(c_28, plain, (r1_tsep_1('#skF_5', '#skF_4') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_46, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 2.72/1.63  tff(c_81, plain, (![B_47, A_48]: (r1_tsep_1(B_47, A_48) | ~r1_tsep_1(A_48, B_47) | ~l1_struct_0(B_47) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.63  tff(c_84, plain, (r1_tsep_1('#skF_5', '#skF_4') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_81])).
% 2.72/1.63  tff(c_85, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 2.72/1.63  tff(c_88, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_85])).
% 2.72/1.63  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_88])).
% 2.72/1.63  tff(c_94, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 2.72/1.63  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_59, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.72/1.63  tff(c_68, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_59])).
% 2.72/1.63  tff(c_93, plain, (~l1_struct_0('#skF_5') | r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 2.72/1.63  tff(c_104, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_93])).
% 2.72/1.63  tff(c_107, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_104])).
% 2.72/1.63  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_107])).
% 2.72/1.63  tff(c_113, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_93])).
% 2.72/1.63  tff(c_20, plain, (![A_17, B_19]: (r1_xboole_0(u1_struct_0(A_17), u1_struct_0(B_19)) | ~r1_tsep_1(A_17, B_19) | ~l1_struct_0(B_19) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.72/1.63  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.72/1.63  tff(c_131, plain, (![B_60, C_61, A_62]: (r1_tarski(u1_struct_0(B_60), u1_struct_0(C_61)) | ~m1_pre_topc(B_60, C_61) | ~m1_pre_topc(C_61, A_62) | ~m1_pre_topc(B_60, A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.72/1.63  tff(c_135, plain, (![B_60]: (r1_tarski(u1_struct_0(B_60), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_60, '#skF_5') | ~m1_pre_topc(B_60, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_131])).
% 2.72/1.63  tff(c_155, plain, (![B_64]: (r1_tarski(u1_struct_0(B_64), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_64, '#skF_5') | ~m1_pre_topc(B_64, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_135])).
% 2.72/1.63  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.63  tff(c_164, plain, (![B_65]: (k3_xboole_0(u1_struct_0(B_65), u1_struct_0('#skF_5'))=u1_struct_0(B_65) | ~m1_pre_topc(B_65, '#skF_5') | ~m1_pre_topc(B_65, '#skF_3'))), inference(resolution, [status(thm)], [c_155, c_10])).
% 2.72/1.63  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.63  tff(c_74, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, k3_xboole_0(A_42, B_43)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.63  tff(c_79, plain, (![A_42, B_43]: (~r1_xboole_0(A_42, B_43) | v1_xboole_0(k3_xboole_0(A_42, B_43)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.72/1.63  tff(c_213, plain, (![B_68]: (~r1_xboole_0(u1_struct_0(B_68), u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0(B_68)) | ~m1_pre_topc(B_68, '#skF_5') | ~m1_pre_topc(B_68, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_164, c_79])).
% 2.72/1.63  tff(c_220, plain, (![A_17]: (v1_xboole_0(u1_struct_0(A_17)) | ~m1_pre_topc(A_17, '#skF_5') | ~m1_pre_topc(A_17, '#skF_3') | ~r1_tsep_1(A_17, '#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0(A_17))), inference(resolution, [status(thm)], [c_20, c_213])).
% 2.72/1.63  tff(c_255, plain, (![A_74]: (v1_xboole_0(u1_struct_0(A_74)) | ~m1_pre_topc(A_74, '#skF_5') | ~m1_pre_topc(A_74, '#skF_3') | ~r1_tsep_1(A_74, '#skF_5') | ~l1_struct_0(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_220])).
% 2.72/1.63  tff(c_16, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.63  tff(c_264, plain, (![A_75]: (v2_struct_0(A_75) | ~m1_pre_topc(A_75, '#skF_5') | ~m1_pre_topc(A_75, '#skF_3') | ~r1_tsep_1(A_75, '#skF_5') | ~l1_struct_0(A_75))), inference(resolution, [status(thm)], [c_255, c_16])).
% 2.72/1.63  tff(c_267, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_264])).
% 2.72/1.63  tff(c_270, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_30, c_267])).
% 2.72/1.63  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_270])).
% 2.72/1.63  tff(c_274, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 2.72/1.63  tff(c_273, plain, (r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.72/1.63  tff(c_309, plain, (![B_89, A_90]: (r1_tsep_1(B_89, A_90) | ~r1_tsep_1(A_90, B_89) | ~l1_struct_0(B_89) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.72/1.63  tff(c_311, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_273, c_309])).
% 2.72/1.63  tff(c_314, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_274, c_311])).
% 2.72/1.63  tff(c_315, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_314])).
% 2.72/1.63  tff(c_318, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_315])).
% 2.72/1.63  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_296, c_318])).
% 2.72/1.63  tff(c_323, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_314])).
% 2.72/1.63  tff(c_327, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_323])).
% 2.72/1.63  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_327])).
% 2.72/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.63  
% 2.72/1.63  Inference rules
% 2.72/1.63  ----------------------
% 2.72/1.63  #Ref     : 0
% 2.72/1.63  #Sup     : 51
% 2.72/1.63  #Fact    : 0
% 2.72/1.63  #Define  : 0
% 2.72/1.63  #Split   : 5
% 2.72/1.63  #Chain   : 0
% 2.72/1.63  #Close   : 0
% 2.72/1.63  
% 2.72/1.63  Ordering : KBO
% 2.72/1.63  
% 2.72/1.63  Simplification rules
% 2.72/1.63  ----------------------
% 2.72/1.63  #Subsume      : 1
% 2.72/1.63  #Demod        : 28
% 2.72/1.63  #Tautology    : 16
% 2.72/1.63  #SimpNegUnit  : 2
% 2.72/1.63  #BackRed      : 0
% 2.72/1.63  
% 2.72/1.63  #Partial instantiations: 0
% 2.72/1.63  #Strategies tried      : 1
% 2.72/1.63  
% 2.72/1.63  Timing (in seconds)
% 2.72/1.63  ----------------------
% 2.72/1.63  Preprocessing        : 0.46
% 2.72/1.63  Parsing              : 0.25
% 2.72/1.63  CNF conversion       : 0.04
% 2.72/1.63  Main loop            : 0.26
% 2.72/1.63  Inferencing          : 0.11
% 2.72/1.63  Reduction            : 0.07
% 2.72/1.63  Demodulation         : 0.05
% 2.72/1.63  BG Simplification    : 0.03
% 2.72/1.63  Subsumption          : 0.04
% 2.72/1.63  Abstraction          : 0.01
% 2.72/1.63  MUC search           : 0.00
% 2.72/1.63  Cooper               : 0.00
% 2.72/1.63  Total                : 0.75
% 2.72/1.63  Index Insertion      : 0.00
% 2.72/1.63  Index Deletion       : 0.00
% 2.72/1.63  Index Matching       : 0.00
% 2.72/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
