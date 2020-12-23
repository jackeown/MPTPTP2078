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
% DateTime   : Thu Dec  3 10:21:53 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   25 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 389 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_tops_1,type,(
    v2_tops_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tops_1(B,A)
            <=> ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r1_tarski(C,B)
                      & v3_pre_topc(C,A) )
                   => C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(c_26,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_91,plain,(
    ! [B_42,A_43] :
      ( v2_tops_1(B_42,A_43)
      | k1_tops_1(A_43,B_42) != k1_xboole_0
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_97,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_94])).

tff(c_98,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_97])).

tff(c_59,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_tops_1(A_38,B_39),B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_64,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_61])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    ! [A_40,B_41] :
      ( v3_pre_topc(k1_tops_1(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_84,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_81])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tops_1(A_5,B_6),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_44,plain,(
    ! [C_29] :
      ( v2_tops_1('#skF_2','#skF_1')
      | k1_xboole_0 = C_29
      | ~ v3_pre_topc(C_29,'#skF_1')
      | ~ r1_tarski(C_29,'#skF_2')
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_123,plain,(
    ! [C_48] :
      ( k1_xboole_0 = C_48
      | ~ v3_pre_topc(C_48,'#skF_1')
      | ~ r1_tarski(C_48,'#skF_2')
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_44])).

tff(c_127,plain,(
    ! [B_6] :
      ( k1_tops_1('#skF_1',B_6) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_6),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_6),'#skF_2')
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_123])).

tff(c_177,plain,(
    ! [B_57] :
      ( k1_tops_1('#skF_1',B_57) = k1_xboole_0
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_57),'#skF_1')
      | ~ r1_tarski(k1_tops_1('#skF_1',B_57),'#skF_2')
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_127])).

tff(c_184,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_177])).

tff(c_190,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_84,c_184])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_190])).

tff(c_193,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_194,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_32,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_223,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_233,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tops_1(A_66,B_67),B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_235,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_223,c_233])).

tff(c_240,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_235])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_251,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_240,c_4])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_262,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_6])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_262])).

tff(c_28,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_28])).

tff(c_30,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_198,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_30])).

tff(c_315,plain,(
    ! [A_74,B_75] :
      ( k1_tops_1(A_74,B_75) = k1_xboole_0
      | ~ v2_tops_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_324,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_315])).

tff(c_332,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_194,c_324])).

tff(c_418,plain,(
    ! [B_78,A_79,C_80] :
      ( r1_tarski(B_78,k1_tops_1(A_79,C_80))
      | ~ r1_tarski(B_78,C_80)
      | ~ v3_pre_topc(B_78,A_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_426,plain,(
    ! [B_78] :
      ( r1_tarski(B_78,k1_tops_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_78,'#skF_2')
      | ~ v3_pre_topc(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_418])).

tff(c_437,plain,(
    ! [B_81] :
      ( r1_tarski(B_81,k1_xboole_0)
      | ~ r1_tarski(B_81,'#skF_2')
      | ~ v3_pre_topc(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_332,c_426])).

tff(c_447,plain,
    ( r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_223,c_437])).

tff(c_459,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_198,c_447])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_459])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  %$ v3_pre_topc > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.39  
% 2.65/1.39  %Foreground sorts:
% 2.65/1.39  
% 2.65/1.39  
% 2.65/1.39  %Background operators:
% 2.65/1.39  
% 2.65/1.39  
% 2.65/1.39  %Foreground operators:
% 2.65/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.39  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.65/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.39  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.39  
% 2.65/1.41  tff(f_96, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v3_pre_topc(C, A)) => (C = k1_xboole_0))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tops_1)).
% 2.65/1.41  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.65/1.41  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.65/1.41  tff(f_47, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.65/1.41  tff(f_39, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 2.65/1.41  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.65/1.41  tff(f_33, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.65/1.41  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 2.65/1.41  tff(c_26, plain, (k1_xboole_0!='#skF_3' | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_45, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.65/1.41  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_91, plain, (![B_42, A_43]: (v2_tops_1(B_42, A_43) | k1_tops_1(A_43, B_42)!=k1_xboole_0 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.41  tff(c_94, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_91])).
% 2.65/1.41  tff(c_97, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_94])).
% 2.65/1.41  tff(c_98, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_45, c_97])).
% 2.65/1.41  tff(c_59, plain, (![A_38, B_39]: (r1_tarski(k1_tops_1(A_38, B_39), B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.41  tff(c_61, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_59])).
% 2.65/1.41  tff(c_64, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_61])).
% 2.65/1.41  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_79, plain, (![A_40, B_41]: (v3_pre_topc(k1_tops_1(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.41  tff(c_81, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_79])).
% 2.65/1.41  tff(c_84, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_81])).
% 2.65/1.41  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(k1_tops_1(A_5, B_6), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.41  tff(c_44, plain, (![C_29]: (v2_tops_1('#skF_2', '#skF_1') | k1_xboole_0=C_29 | ~v3_pre_topc(C_29, '#skF_1') | ~r1_tarski(C_29, '#skF_2') | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_123, plain, (![C_48]: (k1_xboole_0=C_48 | ~v3_pre_topc(C_48, '#skF_1') | ~r1_tarski(C_48, '#skF_2') | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_45, c_44])).
% 2.65/1.41  tff(c_127, plain, (![B_6]: (k1_tops_1('#skF_1', B_6)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_6), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_6), '#skF_2') | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_8, c_123])).
% 2.65/1.41  tff(c_177, plain, (![B_57]: (k1_tops_1('#skF_1', B_57)=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', B_57), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', B_57), '#skF_2') | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_127])).
% 2.65/1.41  tff(c_184, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_2'), '#skF_1') | ~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_177])).
% 2.65/1.41  tff(c_190, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_84, c_184])).
% 2.65/1.41  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_190])).
% 2.65/1.41  tff(c_193, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.65/1.41  tff(c_194, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.65/1.41  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_223, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_32])).
% 2.65/1.41  tff(c_233, plain, (![A_66, B_67]: (r1_tarski(k1_tops_1(A_66, B_67), B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.65/1.41  tff(c_235, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_223, c_233])).
% 2.65/1.41  tff(c_240, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_235])).
% 2.65/1.41  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.65/1.41  tff(c_251, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_240, c_4])).
% 2.65/1.41  tff(c_6, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.65/1.41  tff(c_262, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_6])).
% 2.65/1.41  tff(c_266, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_193, c_262])).
% 2.65/1.41  tff(c_28, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_196, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_28])).
% 2.65/1.41  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_2') | ~v2_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.41  tff(c_198, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_30])).
% 2.65/1.41  tff(c_315, plain, (![A_74, B_75]: (k1_tops_1(A_74, B_75)=k1_xboole_0 | ~v2_tops_1(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.65/1.41  tff(c_324, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_315])).
% 2.65/1.41  tff(c_332, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_194, c_324])).
% 2.65/1.41  tff(c_418, plain, (![B_78, A_79, C_80]: (r1_tarski(B_78, k1_tops_1(A_79, C_80)) | ~r1_tarski(B_78, C_80) | ~v3_pre_topc(B_78, A_79) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.65/1.41  tff(c_426, plain, (![B_78]: (r1_tarski(B_78, k1_tops_1('#skF_1', '#skF_2')) | ~r1_tarski(B_78, '#skF_2') | ~v3_pre_topc(B_78, '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_418])).
% 2.65/1.41  tff(c_437, plain, (![B_81]: (r1_tarski(B_81, k1_xboole_0) | ~r1_tarski(B_81, '#skF_2') | ~v3_pre_topc(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_332, c_426])).
% 2.65/1.41  tff(c_447, plain, (r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_3', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_223, c_437])).
% 2.65/1.41  tff(c_459, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_198, c_447])).
% 2.65/1.41  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_459])).
% 2.65/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.41  
% 2.65/1.41  Inference rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Ref     : 0
% 2.65/1.41  #Sup     : 88
% 2.65/1.41  #Fact    : 0
% 2.65/1.41  #Define  : 0
% 2.65/1.41  #Split   : 7
% 2.65/1.41  #Chain   : 0
% 2.65/1.41  #Close   : 0
% 2.65/1.41  
% 2.65/1.41  Ordering : KBO
% 2.65/1.41  
% 2.65/1.41  Simplification rules
% 2.65/1.41  ----------------------
% 2.65/1.41  #Subsume      : 15
% 2.65/1.41  #Demod        : 57
% 2.65/1.41  #Tautology    : 29
% 2.65/1.41  #SimpNegUnit  : 10
% 2.65/1.41  #BackRed      : 3
% 2.65/1.41  
% 2.65/1.41  #Partial instantiations: 0
% 2.65/1.41  #Strategies tried      : 1
% 2.65/1.41  
% 2.65/1.41  Timing (in seconds)
% 2.65/1.41  ----------------------
% 2.65/1.41  Preprocessing        : 0.28
% 2.65/1.41  Parsing              : 0.15
% 2.65/1.41  CNF conversion       : 0.02
% 2.65/1.41  Main loop            : 0.28
% 2.65/1.41  Inferencing          : 0.11
% 2.65/1.41  Reduction            : 0.08
% 2.65/1.41  Demodulation         : 0.05
% 2.65/1.41  BG Simplification    : 0.02
% 2.65/1.41  Subsumption          : 0.05
% 2.65/1.41  Abstraction          : 0.01
% 2.65/1.41  MUC search           : 0.00
% 2.65/1.41  Cooper               : 0.00
% 2.65/1.41  Total                : 0.59
% 2.65/1.41  Index Insertion      : 0.00
% 2.65/1.41  Index Deletion       : 0.00
% 2.65/1.41  Index Matching       : 0.00
% 2.65/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
