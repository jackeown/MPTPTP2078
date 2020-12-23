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
% DateTime   : Thu Dec  3 10:22:04 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 135 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 314 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tops_1,type,(
    v3_tops_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,
    ( k2_tops_1('#skF_4','#skF_5') != '#skF_5'
    | ~ v3_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_63,plain,(
    ~ v3_tops_1('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,
    ( v3_tops_1('#skF_5','#skF_4')
    | k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_64,plain,(
    k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_60])).

tff(c_216,plain,(
    ! [B_75,A_76] :
      ( v2_tops_1(B_75,A_76)
      | ~ r1_tarski(B_75,k2_tops_1(A_76,B_75))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_221,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_216])).

tff(c_224,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_30,c_221])).

tff(c_48,plain,(
    v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_637,plain,(
    ! [B_100,A_101] :
      ( v3_tops_1(B_100,A_101)
      | ~ v4_pre_topc(B_100,A_101)
      | ~ v2_tops_1(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_640,plain,
    ( v3_tops_1('#skF_5','#skF_4')
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_637])).

tff(c_643,plain,(
    v3_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_224,c_48,c_640])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_643])).

tff(c_646,plain,(
    k2_tops_1('#skF_4','#skF_5') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_647,plain,(
    v3_tops_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_753,plain,(
    ! [B_132,A_133] :
      ( v2_tops_1(B_132,A_133)
      | ~ v3_tops_1(B_132,A_133)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_756,plain,
    ( v2_tops_1('#skF_5','#skF_4')
    | ~ v3_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_753])).

tff(c_759,plain,(
    v2_tops_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_647,c_756])).

tff(c_882,plain,(
    ! [B_150,A_151] :
      ( r1_tarski(B_150,k2_tops_1(A_151,B_150))
      | ~ v2_tops_1(B_150,A_151)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_884,plain,
    ( r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5'))
    | ~ v2_tops_1('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_882])).

tff(c_887,plain,(
    r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_759,c_884])).

tff(c_681,plain,(
    ! [A_117,B_118,C_119] :
      ( k7_subset_1(A_117,B_118,C_119) = k4_xboole_0(B_118,C_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_684,plain,(
    ! [C_119] : k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',C_119) = k4_xboole_0('#skF_5',C_119) ),
    inference(resolution,[status(thm)],[c_50,c_681])).

tff(c_777,plain,(
    ! [A_139,B_140] :
      ( k2_pre_topc(A_139,B_140) = B_140
      | ~ v4_pre_topc(B_140,A_139)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_780,plain,
    ( k2_pre_topc('#skF_4','#skF_5') = '#skF_5'
    | ~ v4_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_777])).

tff(c_783,plain,(
    k2_pre_topc('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_780])).

tff(c_2069,plain,(
    ! [A_214,B_215] :
      ( k7_subset_1(u1_struct_0(A_214),k2_pre_topc(A_214,B_215),k1_tops_1(A_214,B_215)) = k2_tops_1(A_214,B_215)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ l1_pre_topc(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2078,plain,
    ( k7_subset_1(u1_struct_0('#skF_4'),'#skF_5',k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_2069])).

tff(c_2082,plain,(
    k4_xboole_0('#skF_5',k1_tops_1('#skF_4','#skF_5')) = k2_tops_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_684,c_2078])).

tff(c_652,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_1'(A_108,B_109),A_108)
      | r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_730,plain,(
    ! [A_127,B_128,B_129] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_127,B_128),B_129),A_127)
      | r1_tarski(k4_xboole_0(A_127,B_128),B_129) ) ),
    inference(resolution,[status(thm)],[c_652,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_749,plain,(
    ! [A_130,B_131] : r1_tarski(k4_xboole_0(A_130,B_131),A_130) ),
    inference(resolution,[status(thm)],[c_730,c_4])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( B_13 = A_12
      | ~ r1_tarski(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_752,plain,(
    ! [A_130,B_131] :
      ( k4_xboole_0(A_130,B_131) = A_130
      | ~ r1_tarski(A_130,k4_xboole_0(A_130,B_131)) ) ),
    inference(resolution,[status(thm)],[c_749,c_26])).

tff(c_2091,plain,
    ( k4_xboole_0('#skF_5',k1_tops_1('#skF_4','#skF_5')) = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_tops_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2082,c_752])).

tff(c_2112,plain,(
    k2_tops_1('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_2082,c_2091])).

tff(c_2114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_2112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n014.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 13:33:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.72/1.66  
% 3.72/1.66  %Foreground sorts:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Background operators:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Foreground operators:
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.66  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.72/1.66  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.72/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.66  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.72/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.66  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.72/1.66  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.72/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.72/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.66  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.72/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.72/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.72/1.66  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.72/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.66  
% 3.72/1.67  tff(f_115, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.72/1.67  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.72/1.67  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.72/1.67  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_tops_1)).
% 3.72/1.67  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.72/1.67  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.72/1.67  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.72/1.67  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.72/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.72/1.67  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.72/1.67  tff(c_54, plain, (k2_tops_1('#skF_4', '#skF_5')!='#skF_5' | ~v3_tops_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.72/1.67  tff(c_63, plain, (~v3_tops_1('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.72/1.67  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.72/1.67  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.72/1.67  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.72/1.67  tff(c_60, plain, (v3_tops_1('#skF_5', '#skF_4') | k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.72/1.67  tff(c_64, plain, (k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_63, c_60])).
% 3.72/1.67  tff(c_216, plain, (![B_75, A_76]: (v2_tops_1(B_75, A_76) | ~r1_tarski(B_75, k2_tops_1(A_76, B_75)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.72/1.67  tff(c_221, plain, (v2_tops_1('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_64, c_216])).
% 3.72/1.67  tff(c_224, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_30, c_221])).
% 3.72/1.67  tff(c_48, plain, (v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.72/1.67  tff(c_637, plain, (![B_100, A_101]: (v3_tops_1(B_100, A_101) | ~v4_pre_topc(B_100, A_101) | ~v2_tops_1(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.72/1.67  tff(c_640, plain, (v3_tops_1('#skF_5', '#skF_4') | ~v4_pre_topc('#skF_5', '#skF_4') | ~v2_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_637])).
% 3.72/1.67  tff(c_643, plain, (v3_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_224, c_48, c_640])).
% 3.72/1.67  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_643])).
% 3.72/1.67  tff(c_646, plain, (k2_tops_1('#skF_4', '#skF_5')!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 3.72/1.67  tff(c_647, plain, (v3_tops_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 3.72/1.67  tff(c_753, plain, (![B_132, A_133]: (v2_tops_1(B_132, A_133) | ~v3_tops_1(B_132, A_133) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.72/1.67  tff(c_756, plain, (v2_tops_1('#skF_5', '#skF_4') | ~v3_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_753])).
% 3.72/1.67  tff(c_759, plain, (v2_tops_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_647, c_756])).
% 3.72/1.67  tff(c_882, plain, (![B_150, A_151]: (r1_tarski(B_150, k2_tops_1(A_151, B_150)) | ~v2_tops_1(B_150, A_151) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.72/1.67  tff(c_884, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5')) | ~v2_tops_1('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_882])).
% 3.72/1.67  tff(c_887, plain, (r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_759, c_884])).
% 3.72/1.67  tff(c_681, plain, (![A_117, B_118, C_119]: (k7_subset_1(A_117, B_118, C_119)=k4_xboole_0(B_118, C_119) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.72/1.67  tff(c_684, plain, (![C_119]: (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', C_119)=k4_xboole_0('#skF_5', C_119))), inference(resolution, [status(thm)], [c_50, c_681])).
% 3.72/1.67  tff(c_777, plain, (![A_139, B_140]: (k2_pre_topc(A_139, B_140)=B_140 | ~v4_pre_topc(B_140, A_139) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.72/1.67  tff(c_780, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5' | ~v4_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_777])).
% 3.72/1.67  tff(c_783, plain, (k2_pre_topc('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_780])).
% 3.72/1.67  tff(c_2069, plain, (![A_214, B_215]: (k7_subset_1(u1_struct_0(A_214), k2_pre_topc(A_214, B_215), k1_tops_1(A_214, B_215))=k2_tops_1(A_214, B_215) | ~m1_subset_1(B_215, k1_zfmisc_1(u1_struct_0(A_214))) | ~l1_pre_topc(A_214))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.72/1.67  tff(c_2078, plain, (k7_subset_1(u1_struct_0('#skF_4'), '#skF_5', k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_783, c_2069])).
% 3.72/1.67  tff(c_2082, plain, (k4_xboole_0('#skF_5', k1_tops_1('#skF_4', '#skF_5'))=k2_tops_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_684, c_2078])).
% 3.72/1.67  tff(c_652, plain, (![A_108, B_109]: (r2_hidden('#skF_1'(A_108, B_109), A_108) | r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.72/1.67  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.72/1.67  tff(c_730, plain, (![A_127, B_128, B_129]: (r2_hidden('#skF_1'(k4_xboole_0(A_127, B_128), B_129), A_127) | r1_tarski(k4_xboole_0(A_127, B_128), B_129))), inference(resolution, [status(thm)], [c_652, c_12])).
% 3.72/1.67  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.72/1.67  tff(c_749, plain, (![A_130, B_131]: (r1_tarski(k4_xboole_0(A_130, B_131), A_130))), inference(resolution, [status(thm)], [c_730, c_4])).
% 3.72/1.67  tff(c_26, plain, (![B_13, A_12]: (B_13=A_12 | ~r1_tarski(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.72/1.67  tff(c_752, plain, (![A_130, B_131]: (k4_xboole_0(A_130, B_131)=A_130 | ~r1_tarski(A_130, k4_xboole_0(A_130, B_131)))), inference(resolution, [status(thm)], [c_749, c_26])).
% 3.72/1.67  tff(c_2091, plain, (k4_xboole_0('#skF_5', k1_tops_1('#skF_4', '#skF_5'))='#skF_5' | ~r1_tarski('#skF_5', k2_tops_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2082, c_752])).
% 3.72/1.67  tff(c_2112, plain, (k2_tops_1('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_2082, c_2091])).
% 3.72/1.67  tff(c_2114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_2112])).
% 3.72/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.67  
% 3.72/1.67  Inference rules
% 3.72/1.67  ----------------------
% 3.72/1.67  #Ref     : 0
% 3.72/1.67  #Sup     : 597
% 3.72/1.67  #Fact    : 0
% 3.72/1.67  #Define  : 0
% 3.72/1.67  #Split   : 1
% 3.72/1.67  #Chain   : 0
% 3.72/1.67  #Close   : 0
% 3.72/1.67  
% 3.72/1.67  Ordering : KBO
% 3.72/1.67  
% 3.72/1.67  Simplification rules
% 3.72/1.67  ----------------------
% 3.72/1.67  #Subsume      : 206
% 3.72/1.67  #Demod        : 203
% 3.72/1.67  #Tautology    : 174
% 3.72/1.67  #SimpNegUnit  : 5
% 3.72/1.67  #BackRed      : 0
% 3.72/1.67  
% 3.72/1.67  #Partial instantiations: 0
% 3.72/1.67  #Strategies tried      : 1
% 3.72/1.67  
% 3.72/1.67  Timing (in seconds)
% 3.72/1.67  ----------------------
% 3.72/1.68  Preprocessing        : 0.35
% 3.72/1.68  Parsing              : 0.18
% 3.72/1.68  CNF conversion       : 0.03
% 3.72/1.68  Main loop            : 0.55
% 3.72/1.68  Inferencing          : 0.19
% 3.72/1.68  Reduction            : 0.18
% 3.72/1.68  Demodulation         : 0.14
% 3.72/1.68  BG Simplification    : 0.03
% 3.72/1.68  Subsumption          : 0.11
% 3.72/1.68  Abstraction          : 0.03
% 3.72/1.68  MUC search           : 0.00
% 3.72/1.68  Cooper               : 0.00
% 3.72/1.68  Total                : 0.94
% 3.72/1.68  Index Insertion      : 0.00
% 3.72/1.68  Index Deletion       : 0.00
% 3.72/1.68  Index Matching       : 0.00
% 3.72/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
