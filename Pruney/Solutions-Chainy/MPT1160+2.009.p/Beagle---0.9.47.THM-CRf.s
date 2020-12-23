%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:44 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 105 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  169 ( 351 expanded)
%              Number of equality atoms :   17 (  35 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => k3_orders_2(A,k1_struct_0(A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_orders_2)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_20,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_43,plain,(
    ! [A_35] :
      ( k1_struct_0(A_35) = k1_xboole_0
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [A_36] :
      ( k1_struct_0(A_36) = k1_xboole_0
      | ~ l1_orders_2(A_36) ) ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_52,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_28,plain,(
    k3_orders_2('#skF_2',k1_struct_0('#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_53,plain,(
    k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_28])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k3_orders_2(A_62,B_63,C_64),k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_orders_2(A_62)
      | ~ v5_orders_2(A_62)
      | ~ v4_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_353,plain,(
    ! [A_121,A_122,B_123,C_124] :
      ( m1_subset_1(A_121,u1_struct_0(A_122))
      | ~ r2_hidden(A_121,k3_orders_2(A_122,B_123,C_124))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_118,c_12])).

tff(c_357,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_122,B_123,C_124)),u1_struct_0(A_122))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122)
      | k3_orders_2(A_122,B_123,C_124) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_353])).

tff(c_153,plain,(
    ! [B_73,D_74,A_75,C_76] :
      ( r2_hidden(B_73,D_74)
      | ~ r2_hidden(B_73,k3_orders_2(A_75,D_74,C_76))
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(C_76,u1_struct_0(A_75))
      | ~ m1_subset_1(B_73,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_501,plain,(
    ! [A_151,D_152,C_153] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_151,D_152,C_153)),D_152)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_151,D_152,C_153)),u1_struct_0(A_151))
      | ~ l1_orders_2(A_151)
      | ~ v5_orders_2(A_151)
      | ~ v4_orders_2(A_151)
      | ~ v3_orders_2(A_151)
      | v2_struct_0(A_151)
      | k3_orders_2(A_151,D_152,C_153) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_509,plain,(
    ! [A_154,B_155,C_156] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_154,B_155,C_156)),B_155)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154)
      | k3_orders_2(A_154,B_155,C_156) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_357,c_501])).

tff(c_65,plain,(
    ! [C_42,B_43,A_44] :
      ( ~ v1_xboole_0(C_42)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(C_42))
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [B_5,A_44,A_4] :
      ( ~ v1_xboole_0(B_5)
      | ~ r2_hidden(A_44,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_65])).

tff(c_564,plain,(
    ! [B_157,B_158,C_159,A_160] :
      ( ~ v1_xboole_0(B_157)
      | ~ r1_tarski(B_158,B_157)
      | ~ m1_subset_1(C_159,u1_struct_0(A_160))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_orders_2(A_160)
      | ~ v5_orders_2(A_160)
      | ~ v4_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160)
      | k3_orders_2(A_160,B_158,C_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_509,c_68])).

tff(c_585,plain,(
    ! [A_3,C_159,A_160] :
      ( ~ v1_xboole_0(A_3)
      | ~ m1_subset_1(C_159,u1_struct_0(A_160))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_orders_2(A_160)
      | ~ v5_orders_2(A_160)
      | ~ v4_orders_2(A_160)
      | ~ v3_orders_2(A_160)
      | v2_struct_0(A_160)
      | k3_orders_2(A_160,k1_xboole_0,C_159) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_564])).

tff(c_586,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_2])).

tff(c_599,plain,(
    ! [C_164,A_165] :
      ( ~ m1_subset_1(C_164,u1_struct_0(A_165))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165)
      | k3_orders_2(A_165,k1_xboole_0,C_164) = k1_xboole_0 ) ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_618,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_599])).

tff(c_627,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2',k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_618])).

tff(c_628,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_40,c_627])).

tff(c_631,plain,(
    ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_628])).

tff(c_635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:59:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.45  
% 3.17/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.46  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.17/1.46  
% 3.17/1.46  %Foreground sorts:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Background operators:
% 3.17/1.46  
% 3.17/1.46  
% 3.17/1.46  %Foreground operators:
% 3.17/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.17/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.46  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.17/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.17/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.17/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.17/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.46  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.17/1.46  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.17/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.46  
% 3.17/1.47  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.17/1.47  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.47  tff(f_121, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (k3_orders_2(A, k1_struct_0(A), B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_orders_2)).
% 3.17/1.47  tff(f_78, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.17/1.47  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 3.17/1.47  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.17/1.47  tff(f_74, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.17/1.47  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.17/1.47  tff(f_104, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.17/1.47  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.17/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.17/1.47  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.47  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.47  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_20, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.17/1.47  tff(c_43, plain, (![A_35]: (k1_struct_0(A_35)=k1_xboole_0 | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.47  tff(c_48, plain, (![A_36]: (k1_struct_0(A_36)=k1_xboole_0 | ~l1_orders_2(A_36))), inference(resolution, [status(thm)], [c_20, c_43])).
% 3.17/1.47  tff(c_52, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_48])).
% 3.17/1.47  tff(c_28, plain, (k3_orders_2('#skF_2', k1_struct_0('#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_53, plain, (k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_28])).
% 3.17/1.47  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.17/1.47  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.17/1.47  tff(c_118, plain, (![A_62, B_63, C_64]: (m1_subset_1(k3_orders_2(A_62, B_63, C_64), k1_zfmisc_1(u1_struct_0(A_62))) | ~m1_subset_1(C_64, u1_struct_0(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_orders_2(A_62) | ~v5_orders_2(A_62) | ~v4_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.47  tff(c_12, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.47  tff(c_353, plain, (![A_121, A_122, B_123, C_124]: (m1_subset_1(A_121, u1_struct_0(A_122)) | ~r2_hidden(A_121, k3_orders_2(A_122, B_123, C_124)) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_118, c_12])).
% 3.17/1.47  tff(c_357, plain, (![A_122, B_123, C_124]: (m1_subset_1('#skF_1'(k3_orders_2(A_122, B_123, C_124)), u1_struct_0(A_122)) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122) | k3_orders_2(A_122, B_123, C_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_353])).
% 3.17/1.47  tff(c_153, plain, (![B_73, D_74, A_75, C_76]: (r2_hidden(B_73, D_74) | ~r2_hidden(B_73, k3_orders_2(A_75, D_74, C_76)) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(C_76, u1_struct_0(A_75)) | ~m1_subset_1(B_73, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.17/1.47  tff(c_501, plain, (![A_151, D_152, C_153]: (r2_hidden('#skF_1'(k3_orders_2(A_151, D_152, C_153)), D_152) | ~m1_subset_1(D_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_151, D_152, C_153)), u1_struct_0(A_151)) | ~l1_orders_2(A_151) | ~v5_orders_2(A_151) | ~v4_orders_2(A_151) | ~v3_orders_2(A_151) | v2_struct_0(A_151) | k3_orders_2(A_151, D_152, C_153)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_153])).
% 3.17/1.47  tff(c_509, plain, (![A_154, B_155, C_156]: (r2_hidden('#skF_1'(k3_orders_2(A_154, B_155, C_156)), B_155) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154) | k3_orders_2(A_154, B_155, C_156)=k1_xboole_0)), inference(resolution, [status(thm)], [c_357, c_501])).
% 3.17/1.47  tff(c_65, plain, (![C_42, B_43, A_44]: (~v1_xboole_0(C_42) | ~m1_subset_1(B_43, k1_zfmisc_1(C_42)) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.17/1.47  tff(c_68, plain, (![B_5, A_44, A_4]: (~v1_xboole_0(B_5) | ~r2_hidden(A_44, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_10, c_65])).
% 3.17/1.47  tff(c_564, plain, (![B_157, B_158, C_159, A_160]: (~v1_xboole_0(B_157) | ~r1_tarski(B_158, B_157) | ~m1_subset_1(C_159, u1_struct_0(A_160)) | ~m1_subset_1(B_158, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_orders_2(A_160) | ~v5_orders_2(A_160) | ~v4_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160) | k3_orders_2(A_160, B_158, C_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_509, c_68])).
% 3.17/1.47  tff(c_585, plain, (![A_3, C_159, A_160]: (~v1_xboole_0(A_3) | ~m1_subset_1(C_159, u1_struct_0(A_160)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_orders_2(A_160) | ~v5_orders_2(A_160) | ~v4_orders_2(A_160) | ~v3_orders_2(A_160) | v2_struct_0(A_160) | k3_orders_2(A_160, k1_xboole_0, C_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_564])).
% 3.17/1.47  tff(c_586, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_585])).
% 3.17/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.17/1.47  tff(c_597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_586, c_2])).
% 3.17/1.47  tff(c_599, plain, (![C_164, A_165]: (~m1_subset_1(C_164, u1_struct_0(A_165)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165) | k3_orders_2(A_165, k1_xboole_0, C_164)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_585])).
% 3.17/1.47  tff(c_618, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_599])).
% 3.17/1.47  tff(c_627, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_618])).
% 3.17/1.47  tff(c_628, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_53, c_40, c_627])).
% 3.17/1.47  tff(c_631, plain, (~r1_tarski(k1_xboole_0, u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_628])).
% 3.17/1.47  tff(c_635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_631])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 130
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.47  #Split   : 2
% 3.17/1.47  #Chain   : 0
% 3.17/1.47  #Close   : 0
% 3.17/1.47  
% 3.17/1.47  Ordering : KBO
% 3.17/1.47  
% 3.17/1.47  Simplification rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Subsume      : 40
% 3.17/1.47  #Demod        : 10
% 3.17/1.47  #Tautology    : 11
% 3.17/1.47  #SimpNegUnit  : 3
% 3.17/1.47  #BackRed      : 2
% 3.17/1.47  
% 3.17/1.47  #Partial instantiations: 0
% 3.17/1.47  #Strategies tried      : 1
% 3.17/1.47  
% 3.17/1.47  Timing (in seconds)
% 3.17/1.47  ----------------------
% 3.17/1.47  Preprocessing        : 0.29
% 3.17/1.47  Parsing              : 0.17
% 3.17/1.47  CNF conversion       : 0.02
% 3.17/1.47  Main loop            : 0.42
% 3.17/1.47  Inferencing          : 0.15
% 3.17/1.47  Reduction            : 0.09
% 3.17/1.47  Demodulation         : 0.06
% 3.17/1.47  BG Simplification    : 0.02
% 3.17/1.47  Subsumption          : 0.13
% 3.17/1.47  Abstraction          : 0.02
% 3.17/1.47  MUC search           : 0.00
% 3.17/1.47  Cooper               : 0.00
% 3.17/1.47  Total                : 0.74
% 3.17/1.47  Index Insertion      : 0.00
% 3.17/1.47  Index Deletion       : 0.00
% 3.17/1.47  Index Matching       : 0.00
% 3.17/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
