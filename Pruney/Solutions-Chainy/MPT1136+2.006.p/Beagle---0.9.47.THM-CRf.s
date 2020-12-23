%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 188 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_5 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_14,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_47] :
      ( m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_334,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k4_tarski('#skF_5'(A_130,B_131,C_132,D_133),'#skF_6'(A_130,B_131,C_132,D_133)) = A_130
      | ~ r2_hidden(A_130,D_133)
      | ~ m1_subset_1(D_133,k1_zfmisc_1(k2_zfmisc_1(B_131,C_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_450,plain,(
    ! [A_156,A_157] :
      ( k4_tarski('#skF_5'(A_156,u1_struct_0(A_157),u1_struct_0(A_157),u1_orders_2(A_157)),'#skF_6'(A_156,u1_struct_0(A_157),u1_struct_0(A_157),u1_orders_2(A_157))) = A_156
      | ~ r2_hidden(A_156,u1_orders_2(A_157))
      | ~ l1_orders_2(A_157) ) ),
    inference(resolution,[status(thm)],[c_40,c_334])).

tff(c_12,plain,(
    ! [C_16,D_17,A_3] :
      ( k4_tarski(C_16,D_17) != '#skF_1'(A_3)
      | v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_466,plain,(
    ! [A_156,A_3,A_157] :
      ( A_156 != '#skF_1'(A_3)
      | v1_relat_1(A_3)
      | ~ r2_hidden(A_156,u1_orders_2(A_157))
      | ~ l1_orders_2(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_12])).

tff(c_477,plain,(
    ! [A_161,A_162] :
      ( v1_relat_1(A_161)
      | ~ r2_hidden('#skF_1'(A_161),u1_orders_2(A_162))
      | ~ l1_orders_2(A_162) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_466])).

tff(c_487,plain,(
    ! [A_163] :
      ( ~ l1_orders_2(A_163)
      | v1_relat_1(u1_orders_2(A_163)) ) ),
    inference(resolution,[status(thm)],[c_14,c_477])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_55,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_44,c_55])).

tff(c_64,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_42,plain,(
    ~ r1_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    ! [A_38] :
      ( r1_relat_2(u1_orders_2(A_38),u1_struct_0(A_38))
      | ~ v3_orders_2(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_128,plain,(
    ! [C_79,A_80,B_81] :
      ( r2_hidden(k4_tarski(C_79,C_79),A_80)
      | ~ r2_hidden(C_79,B_81)
      | ~ r1_relat_2(A_80,B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_178,plain,(
    ! [B_92,A_93,A_94] :
      ( r2_hidden(k4_tarski(B_92,B_92),A_93)
      | ~ r1_relat_2(A_93,A_94)
      | ~ v1_relat_1(A_93)
      | ~ m1_subset_1(B_92,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_4,c_128])).

tff(c_286,plain,(
    ! [B_124,A_125] :
      ( r2_hidden(k4_tarski(B_124,B_124),u1_orders_2(A_125))
      | ~ v1_relat_1(u1_orders_2(A_125))
      | ~ m1_subset_1(B_124,u1_struct_0(A_125))
      | v1_xboole_0(u1_struct_0(A_125))
      | ~ v3_orders_2(A_125)
      | ~ l1_orders_2(A_125) ) ),
    inference(resolution,[status(thm)],[c_32,c_178])).

tff(c_34,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(A_39,B_43,C_45)
      | ~ r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_303,plain,(
    ! [A_126,B_127] :
      ( r1_orders_2(A_126,B_127,B_127)
      | ~ v1_relat_1(u1_orders_2(A_126))
      | ~ m1_subset_1(B_127,u1_struct_0(A_126))
      | v1_xboole_0(u1_struct_0(A_126))
      | ~ v3_orders_2(A_126)
      | ~ l1_orders_2(A_126) ) ),
    inference(resolution,[status(thm)],[c_286,c_34])).

tff(c_317,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ v3_orders_2('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_324,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_317])).

tff(c_325,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_42,c_324])).

tff(c_490,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_487,c_325])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_490])).

tff(c_496,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_28,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_499,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_496,c_28])).

tff(c_502,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_499])).

tff(c_505,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_502])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_5 > #skF_2 > #skF_4
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.43  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.80/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.80/1.43  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.80/1.43  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.80/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.80/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.80/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.80/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.43  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.80/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.80/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.43  
% 2.80/1.44  tff(f_118, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.80/1.44  tff(f_101, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.80/1.44  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.80/1.44  tff(f_105, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.80/1.44  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.80/1.44  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.80/1.44  tff(f_85, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 2.80/1.44  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 2.80/1.44  tff(f_97, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 2.80/1.44  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.80/1.44  tff(c_46, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.44  tff(c_38, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.44  tff(c_50, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.44  tff(c_14, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.44  tff(c_40, plain, (![A_47]: (m1_subset_1(u1_orders_2(A_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(A_47)))) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.80/1.44  tff(c_334, plain, (![A_130, B_131, C_132, D_133]: (k4_tarski('#skF_5'(A_130, B_131, C_132, D_133), '#skF_6'(A_130, B_131, C_132, D_133))=A_130 | ~r2_hidden(A_130, D_133) | ~m1_subset_1(D_133, k1_zfmisc_1(k2_zfmisc_1(B_131, C_132))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.44  tff(c_450, plain, (![A_156, A_157]: (k4_tarski('#skF_5'(A_156, u1_struct_0(A_157), u1_struct_0(A_157), u1_orders_2(A_157)), '#skF_6'(A_156, u1_struct_0(A_157), u1_struct_0(A_157), u1_orders_2(A_157)))=A_156 | ~r2_hidden(A_156, u1_orders_2(A_157)) | ~l1_orders_2(A_157))), inference(resolution, [status(thm)], [c_40, c_334])).
% 2.80/1.44  tff(c_12, plain, (![C_16, D_17, A_3]: (k4_tarski(C_16, D_17)!='#skF_1'(A_3) | v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.44  tff(c_466, plain, (![A_156, A_3, A_157]: (A_156!='#skF_1'(A_3) | v1_relat_1(A_3) | ~r2_hidden(A_156, u1_orders_2(A_157)) | ~l1_orders_2(A_157))), inference(superposition, [status(thm), theory('equality')], [c_450, c_12])).
% 2.80/1.44  tff(c_477, plain, (![A_161, A_162]: (v1_relat_1(A_161) | ~r2_hidden('#skF_1'(A_161), u1_orders_2(A_162)) | ~l1_orders_2(A_162))), inference(reflexivity, [status(thm), theory('equality')], [c_466])).
% 2.80/1.44  tff(c_487, plain, (![A_163]: (~l1_orders_2(A_163) | v1_relat_1(u1_orders_2(A_163)))), inference(resolution, [status(thm)], [c_14, c_477])).
% 2.80/1.44  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.44  tff(c_55, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.44  tff(c_63, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_55])).
% 2.80/1.44  tff(c_64, plain, (~v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_63])).
% 2.80/1.44  tff(c_42, plain, (~r1_orders_2('#skF_7', '#skF_8', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.44  tff(c_48, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.80/1.44  tff(c_32, plain, (![A_38]: (r1_relat_2(u1_orders_2(A_38), u1_struct_0(A_38)) | ~v3_orders_2(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.80/1.44  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.44  tff(c_128, plain, (![C_79, A_80, B_81]: (r2_hidden(k4_tarski(C_79, C_79), A_80) | ~r2_hidden(C_79, B_81) | ~r1_relat_2(A_80, B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.80/1.44  tff(c_178, plain, (![B_92, A_93, A_94]: (r2_hidden(k4_tarski(B_92, B_92), A_93) | ~r1_relat_2(A_93, A_94) | ~v1_relat_1(A_93) | ~m1_subset_1(B_92, A_94) | v1_xboole_0(A_94))), inference(resolution, [status(thm)], [c_4, c_128])).
% 2.80/1.44  tff(c_286, plain, (![B_124, A_125]: (r2_hidden(k4_tarski(B_124, B_124), u1_orders_2(A_125)) | ~v1_relat_1(u1_orders_2(A_125)) | ~m1_subset_1(B_124, u1_struct_0(A_125)) | v1_xboole_0(u1_struct_0(A_125)) | ~v3_orders_2(A_125) | ~l1_orders_2(A_125))), inference(resolution, [status(thm)], [c_32, c_178])).
% 2.80/1.44  tff(c_34, plain, (![A_39, B_43, C_45]: (r1_orders_2(A_39, B_43, C_45) | ~r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.80/1.44  tff(c_303, plain, (![A_126, B_127]: (r1_orders_2(A_126, B_127, B_127) | ~v1_relat_1(u1_orders_2(A_126)) | ~m1_subset_1(B_127, u1_struct_0(A_126)) | v1_xboole_0(u1_struct_0(A_126)) | ~v3_orders_2(A_126) | ~l1_orders_2(A_126))), inference(resolution, [status(thm)], [c_286, c_34])).
% 2.80/1.44  tff(c_317, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~v1_relat_1(u1_orders_2('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7')) | ~v3_orders_2('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_44, c_303])).
% 2.80/1.44  tff(c_324, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~v1_relat_1(u1_orders_2('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_317])).
% 2.80/1.44  tff(c_325, plain, (~v1_relat_1(u1_orders_2('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_42, c_324])).
% 2.80/1.44  tff(c_490, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_487, c_325])).
% 2.80/1.44  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_490])).
% 2.80/1.44  tff(c_496, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_63])).
% 2.80/1.44  tff(c_28, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.80/1.44  tff(c_499, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_496, c_28])).
% 2.80/1.44  tff(c_502, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_499])).
% 2.80/1.44  tff(c_505, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_38, c_502])).
% 2.80/1.44  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_505])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 2
% 2.80/1.44  #Sup     : 100
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 1
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 3.01/1.44  
% 3.01/1.44  Ordering : KBO
% 3.01/1.45  
% 3.01/1.45  Simplification rules
% 3.01/1.45  ----------------------
% 3.01/1.45  #Subsume      : 4
% 3.01/1.45  #Demod        : 4
% 3.01/1.45  #Tautology    : 26
% 3.01/1.45  #SimpNegUnit  : 2
% 3.01/1.45  #BackRed      : 0
% 3.01/1.45  
% 3.01/1.45  #Partial instantiations: 0
% 3.01/1.45  #Strategies tried      : 1
% 3.01/1.45  
% 3.01/1.45  Timing (in seconds)
% 3.01/1.45  ----------------------
% 3.02/1.45  Preprocessing        : 0.29
% 3.02/1.45  Parsing              : 0.16
% 3.02/1.45  CNF conversion       : 0.02
% 3.02/1.45  Main loop            : 0.32
% 3.02/1.45  Inferencing          : 0.14
% 3.02/1.45  Reduction            : 0.07
% 3.02/1.45  Demodulation         : 0.05
% 3.02/1.45  BG Simplification    : 0.02
% 3.02/1.45  Subsumption          : 0.07
% 3.02/1.45  Abstraction          : 0.01
% 3.02/1.45  MUC search           : 0.00
% 3.02/1.45  Cooper               : 0.00
% 3.02/1.45  Total                : 0.65
% 3.02/1.45  Index Insertion      : 0.00
% 3.02/1.45  Index Deletion       : 0.00
% 3.02/1.45  Index Matching       : 0.00
% 3.02/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
