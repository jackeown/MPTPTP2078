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
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 270 expanded)
%              Number of leaves         :   38 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  165 ( 962 expanded)
%              Number of equality atoms :    8 (  92 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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

tff(f_124,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_88,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_42,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_40,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_59,plain,(
    ! [A_60,B_61] :
      ( m2_orders_2('#skF_4'(A_60,B_61),A_60,B_61)
      | ~ m1_orders_1(B_61,k1_orders_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_61,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_64,plain,
    ( m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_61])).

tff(c_65,plain,(
    m2_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_64])).

tff(c_74,plain,(
    ! [D_68,A_69,B_70] :
      ( r2_hidden(D_68,k4_orders_2(A_69,B_70))
      | ~ m2_orders_2(D_68,A_69,B_70)
      | ~ m1_orders_1(B_70,k1_orders_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_76,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_68,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_79,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_68,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_76])).

tff(c_81,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_71,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_79])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,k3_tarski(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,k1_xboole_0)
      | ~ r2_hidden(A_57,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_92,plain,(
    ! [D_72] :
      ( r1_tarski(D_72,k1_xboole_0)
      | ~ m2_orders_2(D_72,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_81,c_57])).

tff(c_96,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_65,c_92])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    '#skF_4'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_103,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_65])).

tff(c_66,plain,(
    ! [C_62,A_63,B_64] :
      ( v6_orders_2(C_62,A_63)
      | ~ m2_orders_2(C_62,A_63,B_64)
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_68,plain,
    ( v6_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_66])).

tff(c_71,plain,
    ( v6_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_68])).

tff(c_72,plain,(
    v6_orders_2('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_71])).

tff(c_102,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_72])).

tff(c_124,plain,(
    ! [C_73,A_74,B_75] :
      ( m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m2_orders_2(C_73,A_74,B_75)
      | ~ m1_orders_1(B_75,k1_orders_1(u1_struct_0(A_74)))
      | ~ l1_orders_2(A_74)
      | ~ v5_orders_2(A_74)
      | ~ v4_orders_2(A_74)
      | ~ v3_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_124])).

tff(c_129,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_126])).

tff(c_130,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_129])).

tff(c_131,plain,(
    ! [A_76,B_77] :
      ( ~ m2_orders_2(k1_xboole_0,A_76,B_77)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ v6_orders_2(k1_xboole_0,A_76)
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_133,plain,(
    ! [B_77] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_77)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_130,c_131])).

tff(c_136,plain,(
    ! [B_77] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_77)
      | ~ m1_orders_1(B_77,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_102,c_133])).

tff(c_138,plain,(
    ! [B_78] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_136])).

tff(c_141,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_138])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.24  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.21/1.24  
% 2.21/1.24  %Foreground sorts:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Background operators:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Foreground operators:
% 2.21/1.24  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.21/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.21/1.24  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.24  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.21/1.24  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.21/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.24  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.21/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.21/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.21/1.24  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.21/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.24  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.21/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.21/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.21/1.24  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.21/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.24  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.21/1.24  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.21/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.21/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.24  
% 2.21/1.26  tff(f_142, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.21/1.26  tff(f_124, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.21/1.26  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.21/1.26  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.21/1.26  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.21/1.26  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.21/1.26  tff(f_66, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.21/1.26  tff(c_48, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_46, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_44, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_42, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_40, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_38, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_59, plain, (![A_60, B_61]: (m2_orders_2('#skF_4'(A_60, B_61), A_60, B_61) | ~m1_orders_1(B_61, k1_orders_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.21/1.26  tff(c_61, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_59])).
% 2.21/1.26  tff(c_64, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_61])).
% 2.21/1.26  tff(c_65, plain, (m2_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_48, c_64])).
% 2.21/1.26  tff(c_74, plain, (![D_68, A_69, B_70]: (r2_hidden(D_68, k4_orders_2(A_69, B_70)) | ~m2_orders_2(D_68, A_69, B_70) | ~m1_orders_1(B_70, k1_orders_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.21/1.26  tff(c_76, plain, (![D_68]: (r2_hidden(D_68, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_68, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_74])).
% 2.21/1.26  tff(c_79, plain, (![D_68]: (r2_hidden(D_68, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_68, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_76])).
% 2.21/1.26  tff(c_81, plain, (![D_71]: (r2_hidden(D_71, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_71, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_48, c_79])).
% 2.21/1.26  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.21/1.26  tff(c_54, plain, (![A_57, B_58]: (r1_tarski(A_57, k3_tarski(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.26  tff(c_57, plain, (![A_57]: (r1_tarski(A_57, k1_xboole_0) | ~r2_hidden(A_57, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_54])).
% 2.21/1.26  tff(c_92, plain, (![D_72]: (r1_tarski(D_72, k1_xboole_0) | ~m2_orders_2(D_72, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_81, c_57])).
% 2.21/1.26  tff(c_96, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), k1_xboole_0)), inference(resolution, [status(thm)], [c_65, c_92])).
% 2.21/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.26  tff(c_100, plain, ('#skF_4'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.21/1.26  tff(c_103, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_65])).
% 2.21/1.26  tff(c_66, plain, (![C_62, A_63, B_64]: (v6_orders_2(C_62, A_63) | ~m2_orders_2(C_62, A_63, B_64) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.21/1.26  tff(c_68, plain, (v6_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_65, c_66])).
% 2.21/1.26  tff(c_71, plain, (v6_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_68])).
% 2.21/1.26  tff(c_72, plain, (v6_orders_2('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_71])).
% 2.21/1.26  tff(c_102, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_72])).
% 2.21/1.26  tff(c_124, plain, (![C_73, A_74, B_75]: (m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m2_orders_2(C_73, A_74, B_75) | ~m1_orders_1(B_75, k1_orders_1(u1_struct_0(A_74))) | ~l1_orders_2(A_74) | ~v5_orders_2(A_74) | ~v4_orders_2(A_74) | ~v3_orders_2(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.21/1.26  tff(c_126, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_124])).
% 2.21/1.26  tff(c_129, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_126])).
% 2.21/1.26  tff(c_130, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_48, c_129])).
% 2.21/1.26  tff(c_131, plain, (![A_76, B_77]: (~m2_orders_2(k1_xboole_0, A_76, B_77) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_76))) | ~v6_orders_2(k1_xboole_0, A_76) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.21/1.26  tff(c_133, plain, (![B_77]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_77) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_130, c_131])).
% 2.21/1.26  tff(c_136, plain, (![B_77]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_77) | ~m1_orders_1(B_77, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_102, c_133])).
% 2.21/1.26  tff(c_138, plain, (![B_78]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_136])).
% 2.21/1.26  tff(c_141, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_138])).
% 2.21/1.26  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_141])).
% 2.21/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  Inference rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Ref     : 0
% 2.21/1.26  #Sup     : 18
% 2.21/1.26  #Fact    : 0
% 2.21/1.26  #Define  : 0
% 2.21/1.26  #Split   : 0
% 2.21/1.26  #Chain   : 0
% 2.21/1.26  #Close   : 0
% 2.21/1.26  
% 2.21/1.26  Ordering : KBO
% 2.21/1.26  
% 2.21/1.26  Simplification rules
% 2.21/1.26  ----------------------
% 2.21/1.26  #Subsume      : 0
% 2.21/1.26  #Demod        : 39
% 2.21/1.26  #Tautology    : 8
% 2.21/1.26  #SimpNegUnit  : 7
% 2.21/1.26  #BackRed      : 3
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.26  Preprocessing        : 0.33
% 2.21/1.26  Parsing              : 0.18
% 2.21/1.26  CNF conversion       : 0.03
% 2.21/1.26  Main loop            : 0.16
% 2.21/1.26  Inferencing          : 0.06
% 2.21/1.26  Reduction            : 0.05
% 2.21/1.26  Demodulation         : 0.04
% 2.21/1.26  BG Simplification    : 0.02
% 2.21/1.26  Subsumption          : 0.03
% 2.21/1.26  Abstraction          : 0.01
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.53
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
