%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:05 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 261 expanded)
%              Number of leaves         :   37 ( 121 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 965 expanded)
%              Number of equality atoms :   15 ( 113 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_154,negated_conjecture,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_80,axiom,(
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

tff(f_136,axiom,(
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

tff(f_100,axiom,(
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

tff(f_58,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_78,plain,(
    ! [A_61,B_62] :
      ( m2_orders_2('#skF_4'(A_61,B_62),A_61,B_62)
      | ~ m1_orders_1(B_62,k1_orders_1(u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61)
      | ~ v5_orders_2(A_61)
      | ~ v4_orders_2(A_61)
      | ~ v3_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_80,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_83,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_80])).

tff(c_84,plain,(
    m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_83])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_104,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,k4_orders_2(A_73,B_74))
      | ~ m2_orders_2(D_72,A_73,B_74)
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_106,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_72,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_104])).

tff(c_109,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_72,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_106])).

tff(c_111,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_75,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_109])).

tff(c_32,plain,(
    ! [A_52,B_55] :
      ( k3_tarski(A_52) != k1_xboole_0
      | ~ r2_hidden(B_55,A_52)
      | k1_xboole_0 = B_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_116,plain,(
    ! [D_75] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | k1_xboole_0 = D_75
      | ~ m2_orders_2(D_75,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_111,c_32])).

tff(c_124,plain,(
    ! [D_76] :
      ( k1_xboole_0 = D_76
      | ~ m2_orders_2(D_76,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_128,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_124])).

tff(c_131,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_84])).

tff(c_85,plain,(
    ! [C_63,A_64,B_65] :
      ( v6_orders_2(C_63,A_64)
      | ~ m2_orders_2(C_63,A_64,B_65)
      | ~ m1_orders_1(B_65,k1_orders_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_87,plain,
    ( v6_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_85])).

tff(c_90,plain,
    ( v6_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_87])).

tff(c_91,plain,(
    v6_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_90])).

tff(c_130,plain,(
    v6_orders_2(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_91])).

tff(c_97,plain,(
    ! [C_69,A_70,B_71] :
      ( m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m2_orders_2(C_69,A_70,B_71)
      | ~ m1_orders_1(B_71,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_99,plain,
    ( m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_97])).

tff(c_102,plain,
    ( m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_99])).

tff(c_103,plain,(
    m1_subset_1('#skF_4'('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_102])).

tff(c_129,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_103])).

tff(c_154,plain,(
    ! [A_77,B_78] :
      ( ~ m2_orders_2(k1_xboole_0,A_77,B_78)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ v6_orders_2(k1_xboole_0,A_77)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0(A_77)))
      | ~ l1_orders_2(A_77)
      | ~ v5_orders_2(A_77)
      | ~ v4_orders_2(A_77)
      | ~ v3_orders_2(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    ! [B_78] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_78)
      | ~ v6_orders_2(k1_xboole_0,'#skF_6')
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0('#skF_6')))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_129,c_154])).

tff(c_159,plain,(
    ! [B_78] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_78)
      | ~ m1_orders_1(B_78,k1_orders_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_130,c_156])).

tff(c_161,plain,(
    ! [B_79] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_6',B_79)
      | ~ m1_orders_1(B_79,k1_orders_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_159])).

tff(c_164,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.17/1.30  
% 2.17/1.30  %Foreground sorts:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Background operators:
% 2.17/1.30  
% 2.17/1.30  
% 2.17/1.30  %Foreground operators:
% 2.17/1.30  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.17/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.17/1.30  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.17/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.17/1.30  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.30  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.17/1.30  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.17/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.30  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.17/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.17/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.17/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.30  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.17/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.17/1.30  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.17/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.30  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.17/1.30  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.17/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.17/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.17/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.30  
% 2.17/1.32  tff(f_154, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.17/1.32  tff(f_116, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.17/1.32  tff(f_80, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.17/1.32  tff(f_136, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.17/1.32  tff(f_100, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.17/1.32  tff(f_58, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.17/1.32  tff(c_50, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_48, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_46, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_44, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_42, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_40, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_78, plain, (![A_61, B_62]: (m2_orders_2('#skF_4'(A_61, B_62), A_61, B_62) | ~m1_orders_1(B_62, k1_orders_1(u1_struct_0(A_61))) | ~l1_orders_2(A_61) | ~v5_orders_2(A_61) | ~v4_orders_2(A_61) | ~v3_orders_2(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.17/1.32  tff(c_80, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.17/1.32  tff(c_83, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_80])).
% 2.17/1.32  tff(c_84, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_83])).
% 2.17/1.32  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.17/1.32  tff(c_104, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, k4_orders_2(A_73, B_74)) | ~m2_orders_2(D_72, A_73, B_74) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.17/1.32  tff(c_106, plain, (![D_72]: (r2_hidden(D_72, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_72, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_104])).
% 2.17/1.32  tff(c_109, plain, (![D_72]: (r2_hidden(D_72, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_72, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_106])).
% 2.17/1.32  tff(c_111, plain, (![D_75]: (r2_hidden(D_75, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_75, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_50, c_109])).
% 2.17/1.32  tff(c_32, plain, (![A_52, B_55]: (k3_tarski(A_52)!=k1_xboole_0 | ~r2_hidden(B_55, A_52) | k1_xboole_0=B_55)), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.17/1.32  tff(c_116, plain, (![D_75]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | k1_xboole_0=D_75 | ~m2_orders_2(D_75, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_111, c_32])).
% 2.17/1.32  tff(c_124, plain, (![D_76]: (k1_xboole_0=D_76 | ~m2_orders_2(D_76, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 2.17/1.32  tff(c_128, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_124])).
% 2.17/1.32  tff(c_131, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_84])).
% 2.17/1.32  tff(c_85, plain, (![C_63, A_64, B_65]: (v6_orders_2(C_63, A_64) | ~m2_orders_2(C_63, A_64, B_65) | ~m1_orders_1(B_65, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.17/1.32  tff(c_87, plain, (v6_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_84, c_85])).
% 2.17/1.32  tff(c_90, plain, (v6_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_87])).
% 2.17/1.32  tff(c_91, plain, (v6_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_90])).
% 2.17/1.32  tff(c_130, plain, (v6_orders_2(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_91])).
% 2.17/1.32  tff(c_97, plain, (![C_69, A_70, B_71]: (m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m2_orders_2(C_69, A_70, B_71) | ~m1_orders_1(B_71, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.17/1.32  tff(c_99, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_84, c_97])).
% 2.17/1.32  tff(c_102, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_99])).
% 2.17/1.32  tff(c_103, plain, (m1_subset_1('#skF_4'('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_50, c_102])).
% 2.17/1.32  tff(c_129, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_103])).
% 2.17/1.32  tff(c_154, plain, (![A_77, B_78]: (~m2_orders_2(k1_xboole_0, A_77, B_78) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_77))) | ~v6_orders_2(k1_xboole_0, A_77) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0(A_77))) | ~l1_orders_2(A_77) | ~v5_orders_2(A_77) | ~v4_orders_2(A_77) | ~v3_orders_2(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.32  tff(c_156, plain, (![B_78]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_78) | ~v6_orders_2(k1_xboole_0, '#skF_6') | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_129, c_154])).
% 2.17/1.32  tff(c_159, plain, (![B_78]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_78) | ~m1_orders_1(B_78, k1_orders_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_130, c_156])).
% 2.17/1.32  tff(c_161, plain, (![B_79]: (~m2_orders_2(k1_xboole_0, '#skF_6', B_79) | ~m1_orders_1(B_79, k1_orders_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_159])).
% 2.17/1.32  tff(c_164, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_161])).
% 2.17/1.32  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_164])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 22
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 0
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 0
% 2.17/1.32  #Demod        : 45
% 2.17/1.32  #Tautology    : 13
% 2.17/1.32  #SimpNegUnit  : 8
% 2.17/1.32  #BackRed      : 3
% 2.17/1.32  
% 2.17/1.32  #Partial instantiations: 0
% 2.17/1.32  #Strategies tried      : 1
% 2.17/1.32  
% 2.17/1.32  Timing (in seconds)
% 2.17/1.32  ----------------------
% 2.17/1.32  Preprocessing        : 0.36
% 2.17/1.32  Parsing              : 0.17
% 2.17/1.32  CNF conversion       : 0.04
% 2.17/1.32  Main loop            : 0.19
% 2.17/1.32  Inferencing          : 0.07
% 2.17/1.32  Reduction            : 0.06
% 2.17/1.32  Demodulation         : 0.04
% 2.17/1.32  BG Simplification    : 0.02
% 2.17/1.32  Subsumption          : 0.03
% 2.17/1.32  Abstraction          : 0.01
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.59
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
