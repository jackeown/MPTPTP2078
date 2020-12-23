%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:27 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 264 expanded)
%              Number of leaves         :   38 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 ( 761 expanded)
%              Number of equality atoms :   12 (  95 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C] :
                  ( r2_hidden(C,B)
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_38,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_2] : r1_tarski('#skF_5',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_62,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_20,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_57,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_1'(A_12),A_12)
      | A_12 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_26,plain,(
    ! [A_20] :
      ( v4_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_86,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_86])).

tff(c_101,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_186,plain,(
    ! [A_67] :
      ( m1_subset_1('#skF_2'(A_67),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_191,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_186])).

tff(c_194,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_191])).

tff(c_195,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_194])).

tff(c_14,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
      | ~ r2_hidden(A_7,'#skF_2'('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_195,c_14])).

tff(c_224,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_103,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_52,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_4',D_35)
      | ~ r2_hidden(D_35,'#skF_5')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_109,plain,(
    ! [D_47] :
      ( r2_hidden('#skF_4',D_47)
      | ~ r2_hidden(D_47,'#skF_5')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52])).

tff(c_114,plain,
    ( r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_59,c_109])).

tff(c_145,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_50,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,'#skF_5')
      | ~ r2_hidden('#skF_4',D_35)
      | ~ v4_pre_topc(D_35,'#skF_3')
      | ~ v3_pre_topc(D_35,'#skF_3')
      | ~ m1_subset_1(D_35,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_197,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,'#skF_5')
      | ~ r2_hidden('#skF_4',D_68)
      | ~ v4_pre_topc(D_68,'#skF_3')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_50])).

tff(c_201,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_197])).

tff(c_204,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_201])).

tff(c_232,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_237,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_232])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_237])).

tff(c_242,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_247,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_244])).

tff(c_250,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_250])).

tff(c_253,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_276,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_253])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_276])).

tff(c_329,plain,(
    ! [A_75] : ~ r2_hidden(A_75,'#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_339,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_57,c_329])).

tff(c_34,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0('#skF_2'(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_353,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_34])).

tff(c_366,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_62,c_353])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_366])).

tff(c_370,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_384,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_370,c_16])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  
% 2.53/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.32  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.53/1.32  
% 2.53/1.32  %Foreground sorts:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Background operators:
% 2.53/1.32  
% 2.53/1.32  
% 2.53/1.32  %Foreground operators:
% 2.53/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.53/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.53/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.53/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.53/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.53/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.53/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.53/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.32  
% 2.53/1.34  tff(f_132, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.53/1.34  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.53/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.53/1.34  tff(f_67, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C]: (r2_hidden(C, B) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_mcart_1)).
% 2.53/1.34  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.53/1.34  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.53/1.34  tff(f_71, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.53/1.34  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.53/1.34  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.53/1.34  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.53/1.34  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.53/1.34  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.53/1.34  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.53/1.34  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.53/1.34  tff(c_38, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.53/1.34  tff(c_60, plain, (![A_2]: (r1_tarski('#skF_5', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 2.53/1.34  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.53/1.34  tff(c_62, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 2.53/1.34  tff(c_20, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.53/1.34  tff(c_57, plain, (![A_12]: (r2_hidden('#skF_1'(A_12), A_12) | A_12='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 2.53/1.34  tff(c_26, plain, (![A_20]: (v4_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.34  tff(c_24, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.34  tff(c_86, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.34  tff(c_97, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_pre_topc(A_46))), inference(resolution, [status(thm)], [c_24, c_86])).
% 2.53/1.34  tff(c_101, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_97])).
% 2.53/1.34  tff(c_186, plain, (![A_67]: (m1_subset_1('#skF_2'(A_67), k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.53/1.34  tff(c_191, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_186])).
% 2.53/1.34  tff(c_194, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_191])).
% 2.53/1.34  tff(c_195, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_194])).
% 2.53/1.34  tff(c_14, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.53/1.34  tff(c_221, plain, (![A_7]: (~v1_xboole_0(k2_struct_0('#skF_3')) | ~r2_hidden(A_7, '#skF_2'('#skF_3')))), inference(resolution, [status(thm)], [c_195, c_14])).
% 2.53/1.34  tff(c_224, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_221])).
% 2.53/1.34  tff(c_42, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_103, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42])).
% 2.53/1.34  tff(c_12, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.53/1.34  tff(c_28, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.53/1.34  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.53/1.34  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.53/1.34  tff(c_59, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.53/1.34  tff(c_52, plain, (![D_35]: (r2_hidden('#skF_4', D_35) | ~r2_hidden(D_35, '#skF_5') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_109, plain, (![D_47]: (r2_hidden('#skF_4', D_47) | ~r2_hidden(D_47, '#skF_5') | ~m1_subset_1(D_47, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_52])).
% 2.53/1.34  tff(c_114, plain, (r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_59, c_109])).
% 2.53/1.34  tff(c_145, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_114])).
% 2.53/1.34  tff(c_50, plain, (![D_35]: (r2_hidden(D_35, '#skF_5') | ~r2_hidden('#skF_4', D_35) | ~v4_pre_topc(D_35, '#skF_3') | ~v3_pre_topc(D_35, '#skF_3') | ~m1_subset_1(D_35, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.53/1.34  tff(c_197, plain, (![D_68]: (r2_hidden(D_68, '#skF_5') | ~r2_hidden('#skF_4', D_68) | ~v4_pre_topc(D_68, '#skF_3') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_subset_1(D_68, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_50])).
% 2.53/1.34  tff(c_201, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_59, c_197])).
% 2.53/1.34  tff(c_204, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_145, c_201])).
% 2.53/1.34  tff(c_232, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_204])).
% 2.53/1.34  tff(c_237, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_232])).
% 2.53/1.34  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_237])).
% 2.53/1.34  tff(c_242, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_204])).
% 2.53/1.34  tff(c_244, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.53/1.34  tff(c_247, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_244])).
% 2.53/1.34  tff(c_250, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_247])).
% 2.53/1.34  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_250])).
% 2.53/1.34  tff(c_253, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_242])).
% 2.53/1.34  tff(c_276, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_253])).
% 2.53/1.34  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_276])).
% 2.53/1.34  tff(c_329, plain, (![A_75]: (~r2_hidden(A_75, '#skF_2'('#skF_3')))), inference(splitRight, [status(thm)], [c_221])).
% 2.53/1.34  tff(c_339, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_57, c_329])).
% 2.53/1.34  tff(c_34, plain, (![A_22]: (~v1_xboole_0('#skF_2'(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.53/1.34  tff(c_353, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_339, c_34])).
% 2.53/1.34  tff(c_366, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_62, c_353])).
% 2.53/1.34  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_366])).
% 2.53/1.34  tff(c_370, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_114])).
% 2.53/1.34  tff(c_16, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.34  tff(c_384, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_370, c_16])).
% 2.53/1.34  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_384])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 59
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 7
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 6
% 2.53/1.34  #Demod        : 57
% 2.53/1.34  #Tautology    : 22
% 2.53/1.34  #SimpNegUnit  : 9
% 2.53/1.34  #BackRed      : 14
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.34  Preprocessing        : 0.32
% 2.53/1.34  Parsing              : 0.17
% 2.53/1.34  CNF conversion       : 0.02
% 2.53/1.34  Main loop            : 0.25
% 2.53/1.34  Inferencing          : 0.09
% 2.53/1.34  Reduction            : 0.08
% 2.53/1.34  Demodulation         : 0.06
% 2.53/1.34  BG Simplification    : 0.01
% 2.53/1.34  Subsumption          : 0.04
% 2.53/1.34  Abstraction          : 0.01
% 2.53/1.34  MUC search           : 0.00
% 2.53/1.34  Cooper               : 0.00
% 2.53/1.34  Total                : 0.61
% 2.53/1.34  Index Insertion      : 0.00
% 2.53/1.34  Index Deletion       : 0.00
% 2.53/1.34  Index Matching       : 0.00
% 2.53/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
