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
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 233 expanded)
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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    l1_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_49] :
      ( m1_subset_1(u1_orders_2(A_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(A_49))))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_276,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k4_tarski('#skF_5'(A_125,B_126,C_127,D_128),'#skF_6'(A_125,B_126,C_127,D_128)) = A_125
      | ~ r2_hidden(A_125,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(B_126,C_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_412,plain,(
    ! [A_153,A_154] :
      ( k4_tarski('#skF_5'(A_153,u1_struct_0(A_154),u1_struct_0(A_154),u1_orders_2(A_154)),'#skF_6'(A_153,u1_struct_0(A_154),u1_struct_0(A_154),u1_orders_2(A_154))) = A_153
      | ~ r2_hidden(A_153,u1_orders_2(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(resolution,[status(thm)],[c_36,c_276])).

tff(c_8,plain,(
    ! [C_18,D_19,A_5] :
      ( k4_tarski(C_18,D_19) != '#skF_1'(A_5)
      | v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_428,plain,(
    ! [A_153,A_5,A_154] :
      ( A_153 != '#skF_1'(A_5)
      | v1_relat_1(A_5)
      | ~ r2_hidden(A_153,u1_orders_2(A_154))
      | ~ l1_orders_2(A_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_8])).

tff(c_439,plain,(
    ! [A_158,A_159] :
      ( v1_relat_1(A_158)
      | ~ r2_hidden('#skF_1'(A_158),u1_orders_2(A_159))
      | ~ l1_orders_2(A_159) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_428])).

tff(c_450,plain,(
    ! [A_162] :
      ( ~ l1_orders_2(A_162)
      | v1_relat_1(u1_orders_2(A_162)) ) ),
    inference(resolution,[status(thm)],[c_10,c_439])).

tff(c_38,plain,(
    ~ r1_orders_2('#skF_7','#skF_8','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    v3_orders_2('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_28,plain,(
    ! [A_40] :
      ( r1_relat_2(u1_orders_2(A_40),u1_struct_0(A_40))
      | ~ v3_orders_2(A_40)
      | ~ l1_orders_2(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [C_74,A_75,B_76] :
      ( r2_hidden(k4_tarski(C_74,C_74),A_75)
      | ~ r2_hidden(C_74,B_76)
      | ~ r1_relat_2(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_146,plain,(
    ! [A_91,A_92,B_93] :
      ( r2_hidden(k4_tarski(A_91,A_91),A_92)
      | ~ r1_relat_2(A_92,B_93)
      | ~ v1_relat_1(A_92)
      | v1_xboole_0(B_93)
      | ~ m1_subset_1(A_91,B_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_259,plain,(
    ! [A_123,A_124] :
      ( r2_hidden(k4_tarski(A_123,A_123),u1_orders_2(A_124))
      | ~ v1_relat_1(u1_orders_2(A_124))
      | v1_xboole_0(u1_struct_0(A_124))
      | ~ m1_subset_1(A_123,u1_struct_0(A_124))
      | ~ v3_orders_2(A_124)
      | ~ l1_orders_2(A_124) ) ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_30,plain,(
    ! [A_41,B_45,C_47] :
      ( r1_orders_2(A_41,B_45,C_47)
      | ~ r2_hidden(k4_tarski(B_45,C_47),u1_orders_2(A_41))
      | ~ m1_subset_1(C_47,u1_struct_0(A_41))
      | ~ m1_subset_1(B_45,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_296,plain,(
    ! [A_129,A_130] :
      ( r1_orders_2(A_129,A_130,A_130)
      | ~ v1_relat_1(u1_orders_2(A_129))
      | v1_xboole_0(u1_struct_0(A_129))
      | ~ m1_subset_1(A_130,u1_struct_0(A_129))
      | ~ v3_orders_2(A_129)
      | ~ l1_orders_2(A_129) ) ),
    inference(resolution,[status(thm)],[c_259,c_30])).

tff(c_314,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7'))
    | ~ v3_orders_2('#skF_7')
    | ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_296])).

tff(c_323,plain,
    ( r1_orders_2('#skF_7','#skF_8','#skF_8')
    | ~ v1_relat_1(u1_orders_2('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_314])).

tff(c_324,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_7'))
    | v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_323])).

tff(c_325,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_453,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_450,c_325])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_453])).

tff(c_458,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_24,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_462,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_458,c_24])).

tff(c_465,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_462])).

tff(c_468,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_465])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.37  
% 2.82/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.37  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_8 > #skF_5 > #skF_2 > #skF_4
% 2.82/1.37  
% 2.82/1.37  %Foreground sorts:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Background operators:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Foreground operators:
% 2.82/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.82/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.82/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.82/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.82/1.37  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.82/1.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.82/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.82/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.82/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.37  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.82/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.82/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.37  
% 2.82/1.38  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.82/1.38  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.82/1.38  tff(f_45, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.82/1.38  tff(f_102, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.82/1.38  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 2.82/1.38  tff(f_82, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 2.82/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.82/1.38  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 2.82/1.38  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.82/1.38  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.82/1.38  tff(c_42, plain, (l1_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.38  tff(c_34, plain, (![A_48]: (l1_struct_0(A_48) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.82/1.38  tff(c_46, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.38  tff(c_10, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.38  tff(c_36, plain, (![A_49]: (m1_subset_1(u1_orders_2(A_49), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(A_49)))) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.82/1.38  tff(c_276, plain, (![A_125, B_126, C_127, D_128]: (k4_tarski('#skF_5'(A_125, B_126, C_127, D_128), '#skF_6'(A_125, B_126, C_127, D_128))=A_125 | ~r2_hidden(A_125, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(B_126, C_127))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.38  tff(c_412, plain, (![A_153, A_154]: (k4_tarski('#skF_5'(A_153, u1_struct_0(A_154), u1_struct_0(A_154), u1_orders_2(A_154)), '#skF_6'(A_153, u1_struct_0(A_154), u1_struct_0(A_154), u1_orders_2(A_154)))=A_153 | ~r2_hidden(A_153, u1_orders_2(A_154)) | ~l1_orders_2(A_154))), inference(resolution, [status(thm)], [c_36, c_276])).
% 2.82/1.38  tff(c_8, plain, (![C_18, D_19, A_5]: (k4_tarski(C_18, D_19)!='#skF_1'(A_5) | v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.38  tff(c_428, plain, (![A_153, A_5, A_154]: (A_153!='#skF_1'(A_5) | v1_relat_1(A_5) | ~r2_hidden(A_153, u1_orders_2(A_154)) | ~l1_orders_2(A_154))), inference(superposition, [status(thm), theory('equality')], [c_412, c_8])).
% 2.82/1.38  tff(c_439, plain, (![A_158, A_159]: (v1_relat_1(A_158) | ~r2_hidden('#skF_1'(A_158), u1_orders_2(A_159)) | ~l1_orders_2(A_159))), inference(reflexivity, [status(thm), theory('equality')], [c_428])).
% 2.82/1.38  tff(c_450, plain, (![A_162]: (~l1_orders_2(A_162) | v1_relat_1(u1_orders_2(A_162)))), inference(resolution, [status(thm)], [c_10, c_439])).
% 2.82/1.38  tff(c_38, plain, (~r1_orders_2('#skF_7', '#skF_8', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.38  tff(c_44, plain, (v3_orders_2('#skF_7')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.38  tff(c_40, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.82/1.38  tff(c_28, plain, (![A_40]: (r1_relat_2(u1_orders_2(A_40), u1_struct_0(A_40)) | ~v3_orders_2(A_40) | ~l1_orders_2(A_40))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.82/1.38  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.38  tff(c_90, plain, (![C_74, A_75, B_76]: (r2_hidden(k4_tarski(C_74, C_74), A_75) | ~r2_hidden(C_74, B_76) | ~r1_relat_2(A_75, B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.38  tff(c_146, plain, (![A_91, A_92, B_93]: (r2_hidden(k4_tarski(A_91, A_91), A_92) | ~r1_relat_2(A_92, B_93) | ~v1_relat_1(A_92) | v1_xboole_0(B_93) | ~m1_subset_1(A_91, B_93))), inference(resolution, [status(thm)], [c_4, c_90])).
% 2.82/1.38  tff(c_259, plain, (![A_123, A_124]: (r2_hidden(k4_tarski(A_123, A_123), u1_orders_2(A_124)) | ~v1_relat_1(u1_orders_2(A_124)) | v1_xboole_0(u1_struct_0(A_124)) | ~m1_subset_1(A_123, u1_struct_0(A_124)) | ~v3_orders_2(A_124) | ~l1_orders_2(A_124))), inference(resolution, [status(thm)], [c_28, c_146])).
% 2.82/1.38  tff(c_30, plain, (![A_41, B_45, C_47]: (r1_orders_2(A_41, B_45, C_47) | ~r2_hidden(k4_tarski(B_45, C_47), u1_orders_2(A_41)) | ~m1_subset_1(C_47, u1_struct_0(A_41)) | ~m1_subset_1(B_45, u1_struct_0(A_41)) | ~l1_orders_2(A_41))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.82/1.38  tff(c_296, plain, (![A_129, A_130]: (r1_orders_2(A_129, A_130, A_130) | ~v1_relat_1(u1_orders_2(A_129)) | v1_xboole_0(u1_struct_0(A_129)) | ~m1_subset_1(A_130, u1_struct_0(A_129)) | ~v3_orders_2(A_129) | ~l1_orders_2(A_129))), inference(resolution, [status(thm)], [c_259, c_30])).
% 2.82/1.38  tff(c_314, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~v1_relat_1(u1_orders_2('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7')) | ~v3_orders_2('#skF_7') | ~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_40, c_296])).
% 2.82/1.38  tff(c_323, plain, (r1_orders_2('#skF_7', '#skF_8', '#skF_8') | ~v1_relat_1(u1_orders_2('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_314])).
% 2.82/1.38  tff(c_324, plain, (~v1_relat_1(u1_orders_2('#skF_7')) | v1_xboole_0(u1_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_38, c_323])).
% 2.82/1.38  tff(c_325, plain, (~v1_relat_1(u1_orders_2('#skF_7'))), inference(splitLeft, [status(thm)], [c_324])).
% 2.82/1.38  tff(c_453, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_450, c_325])).
% 2.82/1.38  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_453])).
% 2.82/1.38  tff(c_458, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_324])).
% 2.82/1.38  tff(c_24, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.38  tff(c_462, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_458, c_24])).
% 2.82/1.38  tff(c_465, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_462])).
% 2.82/1.38  tff(c_468, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_34, c_465])).
% 2.82/1.38  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_468])).
% 2.82/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  Inference rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Ref     : 2
% 2.82/1.38  #Sup     : 93
% 2.82/1.38  #Fact    : 0
% 2.82/1.38  #Define  : 0
% 2.82/1.38  #Split   : 1
% 2.82/1.38  #Chain   : 0
% 2.82/1.38  #Close   : 0
% 2.82/1.38  
% 2.82/1.38  Ordering : KBO
% 2.82/1.38  
% 2.82/1.38  Simplification rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Subsume      : 2
% 2.82/1.38  #Demod        : 4
% 2.82/1.38  #Tautology    : 12
% 2.82/1.38  #SimpNegUnit  : 2
% 2.82/1.38  #BackRed      : 0
% 2.82/1.38  
% 2.82/1.38  #Partial instantiations: 0
% 2.82/1.38  #Strategies tried      : 1
% 2.82/1.38  
% 2.82/1.38  Timing (in seconds)
% 2.82/1.38  ----------------------
% 2.82/1.39  Preprocessing        : 0.29
% 2.82/1.39  Parsing              : 0.16
% 2.82/1.39  CNF conversion       : 0.02
% 2.82/1.39  Main loop            : 0.33
% 2.82/1.39  Inferencing          : 0.14
% 2.82/1.39  Reduction            : 0.08
% 2.82/1.39  Demodulation         : 0.05
% 2.82/1.39  BG Simplification    : 0.02
% 2.82/1.39  Subsumption          : 0.06
% 2.82/1.39  Abstraction          : 0.02
% 2.82/1.39  MUC search           : 0.00
% 2.82/1.39  Cooper               : 0.00
% 2.82/1.39  Total                : 0.65
% 2.82/1.39  Index Insertion      : 0.00
% 2.82/1.39  Index Deletion       : 0.00
% 2.82/1.39  Index Matching       : 0.00
% 2.82/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
