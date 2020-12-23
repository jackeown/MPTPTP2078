%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:06 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 239 expanded)
%              Number of leaves         :   41 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  171 ( 716 expanded)
%              Number of equality atoms :   14 ( 104 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

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

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_50,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_59,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k3_tarski(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,k1_xboole_0)
      | ~ r2_hidden(A_61,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_59])).

tff(c_68,plain,
    ( r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0)
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_69,plain,(
    k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_83,plain,(
    ! [A_62,B_63] :
      ( ~ v1_xboole_0(k4_orders_2(A_62,B_63))
      | ~ m1_orders_1(B_63,k1_orders_1(u1_struct_0(A_62)))
      | ~ l1_orders_2(A_62)
      | ~ v5_orders_2(A_62)
      | ~ v4_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_86,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_83])).

tff(c_89,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_2,c_69,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_89])).

tff(c_93,plain,(
    k4_orders_2('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_92,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_5','#skF_6')),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_97,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_102,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6'))
    | k4_orders_2('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_105,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_102])).

tff(c_133,plain,(
    ! [D_72,A_73,B_74] :
      ( m2_orders_2(D_72,A_73,B_74)
      | ~ r2_hidden(D_72,k4_orders_2(A_73,B_74))
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_135,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_105,c_133])).

tff(c_141,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_135])).

tff(c_142,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_141])).

tff(c_36,plain,(
    ! [C_53,A_50,B_51] :
      ( v6_orders_2(C_53,A_50)
      | ~ m2_orders_2(C_53,A_50,B_51)
      | ~ m1_orders_1(B_51,k1_orders_1(u1_struct_0(A_50)))
      | ~ l1_orders_2(A_50)
      | ~ v5_orders_2(A_50)
      | ~ v4_orders_2(A_50)
      | ~ v3_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_145,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_36])).

tff(c_148,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_145])).

tff(c_149,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_148])).

tff(c_167,plain,(
    ! [C_77,A_78,B_79] :
      ( m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m2_orders_2(C_77,A_78,B_79)
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0(A_78)))
      | ~ l1_orders_2(A_78)
      | ~ v5_orders_2(A_78)
      | ~ v4_orders_2(A_78)
      | ~ v3_orders_2(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_169,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_167])).

tff(c_172,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_42,c_169])).

tff(c_173,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_172])).

tff(c_202,plain,(
    ! [A_84,B_85] :
      ( ~ m2_orders_2(k1_xboole_0,A_84,B_85)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ v6_orders_2(k1_xboole_0,A_84)
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0(A_84)))
      | ~ l1_orders_2(A_84)
      | ~ v5_orders_2(A_84)
      | ~ v4_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_204,plain,(
    ! [B_85] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_85)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_173,c_202])).

tff(c_207,plain,(
    ! [B_85] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_85)
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_149,c_204])).

tff(c_216,plain,(
    ! [B_89] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_89)
      | ~ m1_orders_1(B_89,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_207])).

tff(c_219,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_216])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 09:36:30 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  
% 2.22/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.31  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.22/1.31  
% 2.22/1.31  %Foreground sorts:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Background operators:
% 2.22/1.31  
% 2.22/1.31  
% 2.22/1.31  %Foreground operators:
% 2.22/1.31  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.22/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.31  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.22/1.31  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.31  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.22/1.31  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.22/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.22/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.31  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.22/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.31  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.22/1.31  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.22/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.31  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.22/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.22/1.31  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.22/1.31  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.31  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.22/1.31  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.22/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.31  
% 2.48/1.33  tff(f_151, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.48/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.48/1.33  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.48/1.33  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.48/1.33  tff(f_133, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.48/1.33  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.48/1.33  tff(f_97, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.48/1.33  tff(f_117, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.48/1.33  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_orders_2)).
% 2.48/1.33  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_50, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_48, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_46, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_44, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_42, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.48/1.33  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.48/1.33  tff(c_40, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.48/1.33  tff(c_59, plain, (![A_59, B_60]: (r1_tarski(A_59, k3_tarski(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.33  tff(c_63, plain, (![A_61]: (r1_tarski(A_61, k1_xboole_0) | ~r2_hidden(A_61, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_59])).
% 2.48/1.33  tff(c_68, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.48/1.33  tff(c_69, plain, (k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_68])).
% 2.48/1.33  tff(c_83, plain, (![A_62, B_63]: (~v1_xboole_0(k4_orders_2(A_62, B_63)) | ~m1_orders_1(B_63, k1_orders_1(u1_struct_0(A_62))) | ~l1_orders_2(A_62) | ~v5_orders_2(A_62) | ~v4_orders_2(A_62) | ~v3_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_133])).
% 2.48/1.33  tff(c_86, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_83])).
% 2.48/1.33  tff(c_89, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_2, c_69, c_86])).
% 2.48/1.33  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_89])).
% 2.48/1.33  tff(c_93, plain, (k4_orders_2('#skF_5', '#skF_6')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_68])).
% 2.48/1.33  tff(c_92, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_5', '#skF_6')), k1_xboole_0)), inference(splitRight, [status(thm)], [c_68])).
% 2.48/1.33  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.33  tff(c_97, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_6])).
% 2.48/1.33  tff(c_102, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6')) | k4_orders_2('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_97, c_4])).
% 2.48/1.33  tff(c_105, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_93, c_102])).
% 2.48/1.33  tff(c_133, plain, (![D_72, A_73, B_74]: (m2_orders_2(D_72, A_73, B_74) | ~r2_hidden(D_72, k4_orders_2(A_73, B_74)) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.48/1.33  tff(c_135, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_105, c_133])).
% 2.48/1.33  tff(c_141, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_135])).
% 2.48/1.33  tff(c_142, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_141])).
% 2.48/1.33  tff(c_36, plain, (![C_53, A_50, B_51]: (v6_orders_2(C_53, A_50) | ~m2_orders_2(C_53, A_50, B_51) | ~m1_orders_1(B_51, k1_orders_1(u1_struct_0(A_50))) | ~l1_orders_2(A_50) | ~v5_orders_2(A_50) | ~v4_orders_2(A_50) | ~v3_orders_2(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.48/1.33  tff(c_145, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_142, c_36])).
% 2.48/1.33  tff(c_148, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_145])).
% 2.48/1.33  tff(c_149, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_148])).
% 2.48/1.33  tff(c_167, plain, (![C_77, A_78, B_79]: (m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m2_orders_2(C_77, A_78, B_79) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0(A_78))) | ~l1_orders_2(A_78) | ~v5_orders_2(A_78) | ~v4_orders_2(A_78) | ~v3_orders_2(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.48/1.33  tff(c_169, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_142, c_167])).
% 2.48/1.33  tff(c_172, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_42, c_169])).
% 2.48/1.33  tff(c_173, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_172])).
% 2.48/1.33  tff(c_202, plain, (![A_84, B_85]: (~m2_orders_2(k1_xboole_0, A_84, B_85) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_84))) | ~v6_orders_2(k1_xboole_0, A_84) | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0(A_84))) | ~l1_orders_2(A_84) | ~v5_orders_2(A_84) | ~v4_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.33  tff(c_204, plain, (![B_85]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_85) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_173, c_202])).
% 2.48/1.33  tff(c_207, plain, (![B_85]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_85) | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_149, c_204])).
% 2.48/1.33  tff(c_216, plain, (![B_89]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_89) | ~m1_orders_1(B_89, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_207])).
% 2.48/1.33  tff(c_219, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_216])).
% 2.48/1.33  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_219])).
% 2.48/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.33  
% 2.48/1.33  Inference rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Ref     : 0
% 2.48/1.33  #Sup     : 33
% 2.48/1.33  #Fact    : 0
% 2.48/1.33  #Define  : 0
% 2.48/1.33  #Split   : 1
% 2.48/1.33  #Chain   : 0
% 2.48/1.33  #Close   : 0
% 2.48/1.33  
% 2.48/1.33  Ordering : KBO
% 2.48/1.33  
% 2.48/1.33  Simplification rules
% 2.48/1.33  ----------------------
% 2.48/1.33  #Subsume      : 0
% 2.48/1.33  #Demod        : 68
% 2.48/1.33  #Tautology    : 15
% 2.48/1.33  #SimpNegUnit  : 13
% 2.48/1.33  #BackRed      : 3
% 2.48/1.33  
% 2.48/1.33  #Partial instantiations: 0
% 2.48/1.33  #Strategies tried      : 1
% 2.48/1.33  
% 2.48/1.33  Timing (in seconds)
% 2.48/1.33  ----------------------
% 2.48/1.33  Preprocessing        : 0.34
% 2.48/1.33  Parsing              : 0.17
% 2.48/1.33  CNF conversion       : 0.03
% 2.48/1.33  Main loop            : 0.21
% 2.48/1.33  Inferencing          : 0.08
% 2.48/1.33  Reduction            : 0.06
% 2.48/1.33  Demodulation         : 0.05
% 2.48/1.33  BG Simplification    : 0.02
% 2.48/1.33  Subsumption          : 0.03
% 2.48/1.33  Abstraction          : 0.01
% 2.48/1.33  MUC search           : 0.00
% 2.48/1.33  Cooper               : 0.00
% 2.48/1.33  Total                : 0.58
% 2.48/1.33  Index Insertion      : 0.00
% 2.48/1.33  Index Deletion       : 0.00
% 2.48/1.33  Index Matching       : 0.00
% 2.48/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
