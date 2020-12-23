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
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 406 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_116,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_40,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_38,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_85,plain,(
    ! [A_56,B_57] :
      ( m2_orders_2('#skF_3'(A_56,B_57),A_56,B_57)
      | ~ m1_orders_1(B_57,k1_orders_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_87,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_85])).

tff(c_90,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_87])).

tff(c_91,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_90])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_101,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,k4_orders_2(A_64,B_65))
      | ~ m2_orders_2(D_63,A_64,B_65)
      | ~ m1_orders_1(B_65,k1_orders_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_63,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_106,plain,(
    ! [D_63] :
      ( r2_hidden(D_63,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_63,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_103])).

tff(c_124,plain,(
    ! [D_66] :
      ( r2_hidden(D_66,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_66,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_106])).

tff(c_28,plain,(
    ! [A_39,B_42] :
      ( k3_tarski(A_39) != k1_xboole_0
      | ~ r2_hidden(B_42,A_39)
      | k1_xboole_0 = B_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_129,plain,(
    ! [D_66] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_66
      | ~ m2_orders_2(D_66,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_124,c_28])).

tff(c_134,plain,(
    ! [D_67] :
      ( k1_xboole_0 = D_67
      | ~ m2_orders_2(D_67,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_129])).

tff(c_138,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_134])).

tff(c_150,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_91])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_165,plain,(
    ! [B_72,A_73,C_74] :
      ( r2_hidden(k1_funct_1(B_72,u1_struct_0(A_73)),C_74)
      | ~ m2_orders_2(C_74,A_73,B_72)
      | ~ m1_orders_1(B_72,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [B_3,A_55,A_2] :
      ( ~ v1_xboole_0(B_3)
      | ~ r2_hidden(A_55,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_177,plain,(
    ! [B_75,C_76,A_77,B_78] :
      ( ~ v1_xboole_0(B_75)
      | ~ r1_tarski(C_76,B_75)
      | ~ m2_orders_2(C_76,A_77,B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_165,c_84])).

tff(c_180,plain,(
    ! [A_1,A_77,B_78] :
      ( ~ v1_xboole_0(A_1)
      | ~ m2_orders_2(k1_xboole_0,A_77,B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_177])).

tff(c_181,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_2])).

tff(c_190,plain,(
    ! [A_82,B_83] :
      ( ~ m2_orders_2(k1_xboole_0,A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_193,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_190])).

tff(c_196,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_150,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.17/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.31  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.31  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.17/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.17/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.17/1.31  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.17/1.32  tff(f_134, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.17/1.32  tff(f_77, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.17/1.32  tff(f_61, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.17/1.32  tff(f_116, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.17/1.32  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.17/1.32  tff(f_96, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.17/1.32  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.32  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.17/1.32  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.32  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_44, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_42, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_40, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_38, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_36, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_85, plain, (![A_56, B_57]: (m2_orders_2('#skF_3'(A_56, B_57), A_56, B_57) | ~m1_orders_1(B_57, k1_orders_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.17/1.32  tff(c_87, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_85])).
% 2.17/1.32  tff(c_90, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_87])).
% 2.17/1.32  tff(c_91, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_90])).
% 2.17/1.32  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.17/1.32  tff(c_101, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, k4_orders_2(A_64, B_65)) | ~m2_orders_2(D_63, A_64, B_65) | ~m1_orders_1(B_65, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.32  tff(c_103, plain, (![D_63]: (r2_hidden(D_63, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_63, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_101])).
% 2.17/1.32  tff(c_106, plain, (![D_63]: (r2_hidden(D_63, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_63, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_103])).
% 2.17/1.32  tff(c_124, plain, (![D_66]: (r2_hidden(D_66, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_66, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_46, c_106])).
% 2.17/1.32  tff(c_28, plain, (![A_39, B_42]: (k3_tarski(A_39)!=k1_xboole_0 | ~r2_hidden(B_42, A_39) | k1_xboole_0=B_42)), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.17/1.32  tff(c_129, plain, (![D_66]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_66 | ~m2_orders_2(D_66, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_124, c_28])).
% 2.17/1.32  tff(c_134, plain, (![D_67]: (k1_xboole_0=D_67 | ~m2_orders_2(D_67, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_129])).
% 2.17/1.32  tff(c_138, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_134])).
% 2.17/1.32  tff(c_150, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_91])).
% 2.17/1.32  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.17/1.32  tff(c_165, plain, (![B_72, A_73, C_74]: (r2_hidden(k1_funct_1(B_72, u1_struct_0(A_73)), C_74) | ~m2_orders_2(C_74, A_73, B_72) | ~m1_orders_1(B_72, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.17/1.32  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.32  tff(c_81, plain, (![C_53, B_54, A_55]: (~v1_xboole_0(C_53) | ~m1_subset_1(B_54, k1_zfmisc_1(C_53)) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.17/1.32  tff(c_84, plain, (![B_3, A_55, A_2]: (~v1_xboole_0(B_3) | ~r2_hidden(A_55, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_8, c_81])).
% 2.17/1.32  tff(c_177, plain, (![B_75, C_76, A_77, B_78]: (~v1_xboole_0(B_75) | ~r1_tarski(C_76, B_75) | ~m2_orders_2(C_76, A_77, B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_165, c_84])).
% 2.17/1.32  tff(c_180, plain, (![A_1, A_77, B_78]: (~v1_xboole_0(A_1) | ~m2_orders_2(k1_xboole_0, A_77, B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_4, c_177])).
% 2.17/1.32  tff(c_181, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitLeft, [status(thm)], [c_180])).
% 2.17/1.32  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.32  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_2])).
% 2.17/1.32  tff(c_190, plain, (![A_82, B_83]: (~m2_orders_2(k1_xboole_0, A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(splitRight, [status(thm)], [c_180])).
% 2.17/1.32  tff(c_193, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_190])).
% 2.17/1.32  tff(c_196, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_150, c_193])).
% 2.17/1.32  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_196])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 31
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 3
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.33  ----------------------
% 2.17/1.33  #Subsume      : 10
% 2.17/1.33  #Demod        : 20
% 2.17/1.33  #Tautology    : 16
% 2.17/1.33  #SimpNegUnit  : 7
% 2.17/1.33  #BackRed      : 4
% 2.17/1.33  
% 2.17/1.33  #Partial instantiations: 0
% 2.17/1.33  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.17/1.33  Preprocessing        : 0.31
% 2.17/1.33  Parsing              : 0.17
% 2.17/1.33  CNF conversion       : 0.03
% 2.17/1.33  Main loop            : 0.20
% 2.17/1.33  Inferencing          : 0.08
% 2.17/1.33  Reduction            : 0.06
% 2.17/1.33  Demodulation         : 0.04
% 2.17/1.33  BG Simplification    : 0.01
% 2.17/1.33  Subsumption          : 0.03
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.54
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
