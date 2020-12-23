%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:20 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 105 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 323 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_relat_2,type,(
    r4_relat_2: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_orders_2(A,B,C)
                    & r1_orders_2(A,C,B) )
                 => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r4_relat_2(A,B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,C),A) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_38,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [A_61] :
      ( m1_subset_1(u1_orders_2(A_61),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(A_61))))
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_101,plain,(
    ! [A_61] :
      ( v1_relat_1(u1_orders_2(A_61))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(A_61)))
      | ~ l1_orders_2(A_61) ) ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_107,plain,(
    ! [A_61] :
      ( v1_relat_1(u1_orders_2(A_61))
      | ~ l1_orders_2(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_101])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_53,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_62,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_50,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_42,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_40,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30,plain,(
    ! [A_27] :
      ( r4_relat_2(u1_orders_2(A_27),u1_struct_0(A_27))
      | ~ v5_orders_2(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    ! [B_32,C_34,A_28] :
      ( r2_hidden(k4_tarski(B_32,C_34),u1_orders_2(A_28))
      | ~ r1_orders_2(A_28,B_32,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(B_32,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_194,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_hidden(k4_tarski(D_91,C_92),A_93)
      | ~ r2_hidden(k4_tarski(C_92,D_91),A_93)
      | ~ r2_hidden(D_91,B_94)
      | ~ r2_hidden(C_92,B_94)
      | ~ r4_relat_2(A_93,B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_350,plain,(
    ! [C_139,B_140,A_141,B_142] :
      ( C_139 = B_140
      | ~ r2_hidden(k4_tarski(C_139,B_140),u1_orders_2(A_141))
      | ~ r2_hidden(B_140,B_142)
      | ~ r2_hidden(C_139,B_142)
      | ~ r4_relat_2(u1_orders_2(A_141),B_142)
      | ~ v1_relat_1(u1_orders_2(A_141))
      | ~ r1_orders_2(A_141,B_140,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0(A_141))
      | ~ m1_subset_1(B_140,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141) ) ),
    inference(resolution,[status(thm)],[c_34,c_194])).

tff(c_366,plain,(
    ! [C_143,B_144,B_145,A_146] :
      ( C_143 = B_144
      | ~ r2_hidden(C_143,B_145)
      | ~ r2_hidden(B_144,B_145)
      | ~ r4_relat_2(u1_orders_2(A_146),B_145)
      | ~ v1_relat_1(u1_orders_2(A_146))
      | ~ r1_orders_2(A_146,C_143,B_144)
      | ~ r1_orders_2(A_146,B_144,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(A_146))
      | ~ m1_subset_1(B_144,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146) ) ),
    inference(resolution,[status(thm)],[c_34,c_350])).

tff(c_409,plain,(
    ! [B_156,B_155,A_157,A_158] :
      ( B_156 = B_155
      | ~ r2_hidden(B_156,A_157)
      | ~ r4_relat_2(u1_orders_2(A_158),A_157)
      | ~ v1_relat_1(u1_orders_2(A_158))
      | ~ r1_orders_2(A_158,B_155,B_156)
      | ~ r1_orders_2(A_158,B_156,B_155)
      | ~ m1_subset_1(B_155,u1_struct_0(A_158))
      | ~ m1_subset_1(B_156,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ m1_subset_1(B_155,A_157)
      | v1_xboole_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_366])).

tff(c_452,plain,(
    ! [B_168,B_167,A_169,A_170] :
      ( B_168 = B_167
      | ~ r4_relat_2(u1_orders_2(A_169),A_170)
      | ~ v1_relat_1(u1_orders_2(A_169))
      | ~ r1_orders_2(A_169,B_168,B_167)
      | ~ r1_orders_2(A_169,B_167,B_168)
      | ~ m1_subset_1(B_168,u1_struct_0(A_169))
      | ~ m1_subset_1(B_167,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ m1_subset_1(B_168,A_170)
      | ~ m1_subset_1(B_167,A_170)
      | v1_xboole_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_6,c_409])).

tff(c_460,plain,(
    ! [B_172,B_171,A_173] :
      ( B_172 = B_171
      | ~ v1_relat_1(u1_orders_2(A_173))
      | ~ r1_orders_2(A_173,B_171,B_172)
      | ~ r1_orders_2(A_173,B_172,B_171)
      | ~ m1_subset_1(B_171,u1_struct_0(A_173))
      | ~ m1_subset_1(B_172,u1_struct_0(A_173))
      | v1_xboole_0(u1_struct_0(A_173))
      | ~ v5_orders_2(A_173)
      | ~ l1_orders_2(A_173) ) ),
    inference(resolution,[status(thm)],[c_30,c_452])).

tff(c_466,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v5_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_460])).

tff(c_473,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_46,c_44,c_42,c_466])).

tff(c_474,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_38,c_473])).

tff(c_481,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_474])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_481])).

tff(c_486,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_487,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_61,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_488,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_488])).

tff(c_497,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_514,plain,(
    ! [A_176] :
      ( A_176 = '#skF_5'
      | ~ v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_497,c_2])).

tff(c_523,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_486,c_514])).

tff(c_530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:34:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.43  
% 3.36/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.43  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.36/1.43  
% 3.36/1.43  %Foreground sorts:
% 3.36/1.43  
% 3.36/1.43  
% 3.36/1.43  %Background operators:
% 3.36/1.43  
% 3.36/1.43  
% 3.36/1.43  %Foreground operators:
% 3.36/1.43  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 3.36/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.36/1.43  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.36/1.43  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.43  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.36/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.36/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.36/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.43  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.36/1.43  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.36/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.43  
% 3.36/1.45  tff(f_110, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 3.36/1.45  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.45  tff(f_93, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.36/1.45  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.36/1.45  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.36/1.45  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 3.36/1.45  tff(f_89, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.36/1.45  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 3.36/1.45  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.36/1.45  tff(c_38, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_48, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.45  tff(c_98, plain, (![A_61]: (m1_subset_1(u1_orders_2(A_61), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(A_61)))) | ~l1_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.36/1.45  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.36/1.45  tff(c_101, plain, (![A_61]: (v1_relat_1(u1_orders_2(A_61)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(A_61))) | ~l1_orders_2(A_61))), inference(resolution, [status(thm)], [c_98, c_12])).
% 3.36/1.45  tff(c_107, plain, (![A_61]: (v1_relat_1(u1_orders_2(A_61)) | ~l1_orders_2(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_101])).
% 3.36/1.45  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_53, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.45  tff(c_60, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_53])).
% 3.36/1.45  tff(c_62, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.36/1.45  tff(c_50, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_42, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_40, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.45  tff(c_30, plain, (![A_27]: (r4_relat_2(u1_orders_2(A_27), u1_struct_0(A_27)) | ~v5_orders_2(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.36/1.45  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.36/1.45  tff(c_34, plain, (![B_32, C_34, A_28]: (r2_hidden(k4_tarski(B_32, C_34), u1_orders_2(A_28)) | ~r1_orders_2(A_28, B_32, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(B_32, u1_struct_0(A_28)) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.36/1.45  tff(c_194, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_hidden(k4_tarski(D_91, C_92), A_93) | ~r2_hidden(k4_tarski(C_92, D_91), A_93) | ~r2_hidden(D_91, B_94) | ~r2_hidden(C_92, B_94) | ~r4_relat_2(A_93, B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.36/1.45  tff(c_350, plain, (![C_139, B_140, A_141, B_142]: (C_139=B_140 | ~r2_hidden(k4_tarski(C_139, B_140), u1_orders_2(A_141)) | ~r2_hidden(B_140, B_142) | ~r2_hidden(C_139, B_142) | ~r4_relat_2(u1_orders_2(A_141), B_142) | ~v1_relat_1(u1_orders_2(A_141)) | ~r1_orders_2(A_141, B_140, C_139) | ~m1_subset_1(C_139, u1_struct_0(A_141)) | ~m1_subset_1(B_140, u1_struct_0(A_141)) | ~l1_orders_2(A_141))), inference(resolution, [status(thm)], [c_34, c_194])).
% 3.36/1.45  tff(c_366, plain, (![C_143, B_144, B_145, A_146]: (C_143=B_144 | ~r2_hidden(C_143, B_145) | ~r2_hidden(B_144, B_145) | ~r4_relat_2(u1_orders_2(A_146), B_145) | ~v1_relat_1(u1_orders_2(A_146)) | ~r1_orders_2(A_146, C_143, B_144) | ~r1_orders_2(A_146, B_144, C_143) | ~m1_subset_1(C_143, u1_struct_0(A_146)) | ~m1_subset_1(B_144, u1_struct_0(A_146)) | ~l1_orders_2(A_146))), inference(resolution, [status(thm)], [c_34, c_350])).
% 3.36/1.45  tff(c_409, plain, (![B_156, B_155, A_157, A_158]: (B_156=B_155 | ~r2_hidden(B_156, A_157) | ~r4_relat_2(u1_orders_2(A_158), A_157) | ~v1_relat_1(u1_orders_2(A_158)) | ~r1_orders_2(A_158, B_155, B_156) | ~r1_orders_2(A_158, B_156, B_155) | ~m1_subset_1(B_155, u1_struct_0(A_158)) | ~m1_subset_1(B_156, u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~m1_subset_1(B_155, A_157) | v1_xboole_0(A_157))), inference(resolution, [status(thm)], [c_6, c_366])).
% 3.36/1.45  tff(c_452, plain, (![B_168, B_167, A_169, A_170]: (B_168=B_167 | ~r4_relat_2(u1_orders_2(A_169), A_170) | ~v1_relat_1(u1_orders_2(A_169)) | ~r1_orders_2(A_169, B_168, B_167) | ~r1_orders_2(A_169, B_167, B_168) | ~m1_subset_1(B_168, u1_struct_0(A_169)) | ~m1_subset_1(B_167, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~m1_subset_1(B_168, A_170) | ~m1_subset_1(B_167, A_170) | v1_xboole_0(A_170))), inference(resolution, [status(thm)], [c_6, c_409])).
% 3.36/1.45  tff(c_460, plain, (![B_172, B_171, A_173]: (B_172=B_171 | ~v1_relat_1(u1_orders_2(A_173)) | ~r1_orders_2(A_173, B_171, B_172) | ~r1_orders_2(A_173, B_172, B_171) | ~m1_subset_1(B_171, u1_struct_0(A_173)) | ~m1_subset_1(B_172, u1_struct_0(A_173)) | v1_xboole_0(u1_struct_0(A_173)) | ~v5_orders_2(A_173) | ~l1_orders_2(A_173))), inference(resolution, [status(thm)], [c_30, c_452])).
% 3.36/1.45  tff(c_466, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | ~r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v5_orders_2('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_40, c_460])).
% 3.36/1.45  tff(c_473, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_46, c_44, c_42, c_466])).
% 3.36/1.45  tff(c_474, plain, (~v1_relat_1(u1_orders_2('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_38, c_473])).
% 3.36/1.45  tff(c_481, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_107, c_474])).
% 3.36/1.45  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_481])).
% 3.36/1.45  tff(c_486, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.36/1.45  tff(c_487, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 3.36/1.45  tff(c_61, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_53])).
% 3.36/1.45  tff(c_488, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_61])).
% 3.36/1.45  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_487, c_488])).
% 3.36/1.45  tff(c_497, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_61])).
% 3.36/1.45  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.36/1.45  tff(c_514, plain, (![A_176]: (A_176='#skF_5' | ~v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_497, c_2])).
% 3.36/1.45  tff(c_523, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_486, c_514])).
% 3.36/1.45  tff(c_530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_523])).
% 3.36/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.45  
% 3.36/1.45  Inference rules
% 3.36/1.45  ----------------------
% 3.36/1.45  #Ref     : 0
% 3.36/1.45  #Sup     : 110
% 3.36/1.45  #Fact    : 0
% 3.36/1.45  #Define  : 0
% 3.36/1.45  #Split   : 3
% 3.36/1.45  #Chain   : 0
% 3.36/1.45  #Close   : 0
% 3.36/1.45  
% 3.36/1.45  Ordering : KBO
% 3.36/1.45  
% 3.36/1.45  Simplification rules
% 3.36/1.45  ----------------------
% 3.36/1.45  #Subsume      : 9
% 3.36/1.45  #Demod        : 14
% 3.36/1.45  #Tautology    : 27
% 3.36/1.45  #SimpNegUnit  : 3
% 3.36/1.45  #BackRed      : 0
% 3.36/1.45  
% 3.36/1.45  #Partial instantiations: 0
% 3.36/1.45  #Strategies tried      : 1
% 3.36/1.45  
% 3.36/1.45  Timing (in seconds)
% 3.36/1.45  ----------------------
% 3.36/1.45  Preprocessing        : 0.31
% 3.36/1.45  Parsing              : 0.16
% 3.36/1.45  CNF conversion       : 0.02
% 3.36/1.45  Main loop            : 0.39
% 3.36/1.45  Inferencing          : 0.15
% 3.36/1.45  Reduction            : 0.09
% 3.36/1.45  Demodulation         : 0.06
% 3.36/1.45  BG Simplification    : 0.02
% 3.36/1.45  Subsumption          : 0.10
% 3.36/1.45  Abstraction          : 0.02
% 3.36/1.45  MUC search           : 0.00
% 3.36/1.45  Cooper               : 0.00
% 3.36/1.45  Total                : 0.73
% 3.36/1.45  Index Insertion      : 0.00
% 3.36/1.45  Index Deletion       : 0.00
% 3.36/1.45  Index Matching       : 0.00
% 3.36/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
