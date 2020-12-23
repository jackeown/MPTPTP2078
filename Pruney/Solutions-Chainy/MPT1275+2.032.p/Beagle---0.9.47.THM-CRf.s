%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:06 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :    6
%              Number of atoms          :  126 ( 300 expanded)
%              Number of equality atoms :   31 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_52,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_89,plain,(
    ! [A_36,B_37] :
      ( k1_tops_1(A_36,B_37) = k1_xboole_0
      | ~ v2_tops_1(B_37,A_36)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_92,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_95,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_92])).

tff(c_96,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44])).

tff(c_122,plain,(
    ! [B_44,A_45] :
      ( v2_tops_1(B_44,A_45)
      | ~ r1_tarski(B_44,k2_tops_1(A_45,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_124,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_122])).

tff(c_126,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_6,c_124])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_126])).

tff(c_130,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_32,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_135,plain,(
    ! [A_46,B_47] :
      ( k2_pre_topc(A_46,B_47) = B_47
      | ~ v4_pre_topc(B_47,A_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_135])).

tff(c_141,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_138])).

tff(c_159,plain,(
    ! [B_52,A_53] :
      ( v3_tops_1(B_52,A_53)
      | ~ v2_tops_1(k2_pre_topc(A_53,B_52),A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_163,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_130,c_161])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_163])).

tff(c_166,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_167,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_189,plain,(
    ! [B_60,A_61] :
      ( v2_tops_1(B_60,A_61)
      | ~ v3_tops_1(B_60,A_61)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_192,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_189])).

tff(c_195,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_167,c_192])).

tff(c_196,plain,(
    ! [A_62,B_63] :
      ( k1_tops_1(A_62,B_63) = k1_xboole_0
      | ~ v2_tops_1(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_196])).

tff(c_202,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_199])).

tff(c_204,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_202])).

tff(c_176,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_subset_1(A_56,B_57,C_58) = k4_xboole_0(B_57,C_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [C_58] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_58) = k4_xboole_0('#skF_2',C_58) ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_209,plain,(
    ! [A_64,B_65] :
      ( k2_pre_topc(A_64,B_65) = B_65
      | ~ v4_pre_topc(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_212,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_209])).

tff(c_215,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_212])).

tff(c_262,plain,(
    ! [A_78,B_79] :
      ( k7_subset_1(u1_struct_0(A_78),k2_pre_topc(A_78,B_79),k1_tops_1(A_78,B_79)) = k2_tops_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_271,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_262])).

tff(c_278,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_8,c_204,c_179,c_271])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.46  
% 2.55/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.46  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.57/1.46  
% 2.57/1.46  %Foreground sorts:
% 2.57/1.46  
% 2.57/1.46  
% 2.57/1.46  %Background operators:
% 2.57/1.46  
% 2.57/1.46  
% 2.57/1.46  %Foreground operators:
% 2.57/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.46  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.57/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.46  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.57/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.57/1.46  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.57/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.46  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.57/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.46  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.57/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.46  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.57/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.57/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.57/1.46  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.57/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.46  
% 2.57/1.48  tff(f_107, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 2.57/1.48  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.57/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/1.48  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 2.57/1.48  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.57/1.48  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 2.57/1.48  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.57/1.48  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.57/1.48  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.57/1.48  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.57/1.48  tff(c_38, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.57/1.48  tff(c_56, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 2.57/1.48  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.57/1.48  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.57/1.48  tff(c_89, plain, (![A_36, B_37]: (k1_tops_1(A_36, B_37)=k1_xboole_0 | ~v2_tops_1(B_37, A_36) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.57/1.48  tff(c_92, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_89])).
% 2.57/1.48  tff(c_95, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_92])).
% 2.57/1.48  tff(c_96, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_95])).
% 2.57/1.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.48  tff(c_44, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.57/1.48  tff(c_57, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_44])).
% 2.57/1.48  tff(c_122, plain, (![B_44, A_45]: (v2_tops_1(B_44, A_45) | ~r1_tarski(B_44, k2_tops_1(A_45, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.57/1.48  tff(c_124, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_57, c_122])).
% 2.57/1.48  tff(c_126, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_6, c_124])).
% 2.57/1.48  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_126])).
% 2.57/1.48  tff(c_130, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_95])).
% 2.57/1.48  tff(c_32, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.57/1.48  tff(c_135, plain, (![A_46, B_47]: (k2_pre_topc(A_46, B_47)=B_47 | ~v4_pre_topc(B_47, A_46) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.48  tff(c_138, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_135])).
% 2.57/1.48  tff(c_141, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_138])).
% 2.57/1.48  tff(c_159, plain, (![B_52, A_53]: (v3_tops_1(B_52, A_53) | ~v2_tops_1(k2_pre_topc(A_53, B_52), A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.57/1.48  tff(c_161, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 2.57/1.48  tff(c_163, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_130, c_161])).
% 2.57/1.48  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_163])).
% 2.57/1.48  tff(c_166, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.57/1.48  tff(c_8, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.48  tff(c_167, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 2.57/1.48  tff(c_189, plain, (![B_60, A_61]: (v2_tops_1(B_60, A_61) | ~v3_tops_1(B_60, A_61) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.57/1.48  tff(c_192, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_189])).
% 2.57/1.48  tff(c_195, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_167, c_192])).
% 2.57/1.48  tff(c_196, plain, (![A_62, B_63]: (k1_tops_1(A_62, B_63)=k1_xboole_0 | ~v2_tops_1(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.57/1.48  tff(c_199, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_196])).
% 2.57/1.48  tff(c_202, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_199])).
% 2.57/1.48  tff(c_204, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_195, c_202])).
% 2.57/1.48  tff(c_176, plain, (![A_56, B_57, C_58]: (k7_subset_1(A_56, B_57, C_58)=k4_xboole_0(B_57, C_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.48  tff(c_179, plain, (![C_58]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_58)=k4_xboole_0('#skF_2', C_58))), inference(resolution, [status(thm)], [c_34, c_176])).
% 2.57/1.48  tff(c_209, plain, (![A_64, B_65]: (k2_pre_topc(A_64, B_65)=B_65 | ~v4_pre_topc(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.48  tff(c_212, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_209])).
% 2.57/1.48  tff(c_215, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_212])).
% 2.57/1.48  tff(c_262, plain, (![A_78, B_79]: (k7_subset_1(u1_struct_0(A_78), k2_pre_topc(A_78, B_79), k1_tops_1(A_78, B_79))=k2_tops_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.57/1.48  tff(c_271, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_262])).
% 2.57/1.48  tff(c_278, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_8, c_204, c_179, c_271])).
% 2.57/1.48  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_278])).
% 2.57/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.48  
% 2.57/1.48  Inference rules
% 2.57/1.48  ----------------------
% 2.57/1.48  #Ref     : 0
% 2.57/1.48  #Sup     : 46
% 2.57/1.48  #Fact    : 0
% 2.57/1.48  #Define  : 0
% 2.57/1.48  #Split   : 2
% 2.57/1.48  #Chain   : 0
% 2.57/1.48  #Close   : 0
% 2.57/1.48  
% 2.57/1.48  Ordering : KBO
% 2.57/1.48  
% 2.57/1.48  Simplification rules
% 2.57/1.48  ----------------------
% 2.57/1.48  #Subsume      : 2
% 2.57/1.48  #Demod        : 57
% 2.57/1.48  #Tautology    : 33
% 2.57/1.48  #SimpNegUnit  : 6
% 2.57/1.48  #BackRed      : 0
% 2.57/1.48  
% 2.57/1.48  #Partial instantiations: 0
% 2.57/1.48  #Strategies tried      : 1
% 2.57/1.48  
% 2.57/1.48  Timing (in seconds)
% 2.57/1.48  ----------------------
% 2.57/1.48  Preprocessing        : 0.37
% 2.57/1.48  Parsing              : 0.20
% 2.57/1.48  CNF conversion       : 0.03
% 2.57/1.48  Main loop            : 0.24
% 2.57/1.48  Inferencing          : 0.10
% 2.57/1.48  Reduction            : 0.07
% 2.57/1.48  Demodulation         : 0.06
% 2.57/1.48  BG Simplification    : 0.02
% 2.57/1.48  Subsumption          : 0.03
% 2.57/1.48  Abstraction          : 0.01
% 2.57/1.48  MUC search           : 0.00
% 2.57/1.48  Cooper               : 0.00
% 2.57/1.48  Total                : 0.65
% 2.57/1.48  Index Insertion      : 0.00
% 2.57/1.48  Index Deletion       : 0.00
% 2.57/1.48  Index Matching       : 0.00
% 2.57/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
