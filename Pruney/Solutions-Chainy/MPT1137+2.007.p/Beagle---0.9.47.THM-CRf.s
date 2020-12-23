%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 129 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 454 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_120,plain,(
    ! [B_80,C_81,A_82] :
      ( r2_hidden(k4_tarski(B_80,C_81),u1_orders_2(A_82))
      | ~ r1_orders_2(A_82,B_80,C_81)
      | ~ m1_subset_1(C_81,u1_struct_0(A_82))
      | ~ m1_subset_1(B_80,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ v1_xboole_0(u1_orders_2(A_86))
      | ~ r1_orders_2(A_86,B_87,C_88)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86) ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_146,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_144])).

tff(c_151,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_44,c_146])).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_90,plain,(
    ! [A_69] :
      ( m1_subset_1(u1_orders_2(A_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_69),u1_struct_0(A_69))))
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [A_69] :
      ( v1_relat_1(u1_orders_2(A_69))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_69),u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69) ) ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_100,plain,(
    ! [A_69] :
      ( v1_relat_1(u1_orders_2(A_69))
      | ~ l1_orders_2(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_36,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    ! [A_33] :
      ( r4_relat_2(u1_orders_2(A_33),u1_struct_0(A_33))
      | ~ v5_orders_2(A_33)
      | ~ l1_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [B_38,C_40,A_34] :
      ( r2_hidden(k4_tarski(B_38,C_40),u1_orders_2(A_34))
      | ~ r1_orders_2(A_34,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_155,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( D_89 = C_90
      | ~ r2_hidden(k4_tarski(D_89,C_90),A_91)
      | ~ r2_hidden(k4_tarski(C_90,D_89),A_91)
      | ~ r2_hidden(D_89,B_92)
      | ~ r2_hidden(C_90,B_92)
      | ~ r4_relat_2(A_91,B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_287,plain,(
    ! [C_146,B_147,A_148,B_149] :
      ( C_146 = B_147
      | ~ r2_hidden(k4_tarski(C_146,B_147),u1_orders_2(A_148))
      | ~ r2_hidden(B_147,B_149)
      | ~ r2_hidden(C_146,B_149)
      | ~ r4_relat_2(u1_orders_2(A_148),B_149)
      | ~ v1_relat_1(u1_orders_2(A_148))
      | ~ r1_orders_2(A_148,B_147,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_148))
      | ~ m1_subset_1(B_147,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148) ) ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_303,plain,(
    ! [C_150,B_151,B_152,A_153] :
      ( C_150 = B_151
      | ~ r2_hidden(C_150,B_152)
      | ~ r2_hidden(B_151,B_152)
      | ~ r4_relat_2(u1_orders_2(A_153),B_152)
      | ~ v1_relat_1(u1_orders_2(A_153))
      | ~ r1_orders_2(A_153,C_150,B_151)
      | ~ r1_orders_2(A_153,B_151,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0(A_153))
      | ~ m1_subset_1(B_151,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153) ) ),
    inference(resolution,[status(thm)],[c_32,c_287])).

tff(c_325,plain,(
    ! [B_154,A_155,B_156,A_157] :
      ( B_154 = A_155
      | ~ r2_hidden(B_154,B_156)
      | ~ r4_relat_2(u1_orders_2(A_157),B_156)
      | ~ v1_relat_1(u1_orders_2(A_157))
      | ~ r1_orders_2(A_157,A_155,B_154)
      | ~ r1_orders_2(A_157,B_154,A_155)
      | ~ m1_subset_1(A_155,u1_struct_0(A_157))
      | ~ m1_subset_1(B_154,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | v1_xboole_0(B_156)
      | ~ m1_subset_1(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_6,c_303])).

tff(c_349,plain,(
    ! [A_167,A_166,A_168,B_169] :
      ( A_167 = A_166
      | ~ r4_relat_2(u1_orders_2(A_168),B_169)
      | ~ v1_relat_1(u1_orders_2(A_168))
      | ~ r1_orders_2(A_168,A_167,A_166)
      | ~ r1_orders_2(A_168,A_166,A_167)
      | ~ m1_subset_1(A_167,u1_struct_0(A_168))
      | ~ m1_subset_1(A_166,u1_struct_0(A_168))
      | ~ l1_orders_2(A_168)
      | ~ m1_subset_1(A_167,B_169)
      | v1_xboole_0(B_169)
      | ~ m1_subset_1(A_166,B_169) ) ),
    inference(resolution,[status(thm)],[c_6,c_325])).

tff(c_365,plain,(
    ! [A_171,A_170,A_172] :
      ( A_171 = A_170
      | ~ v1_relat_1(u1_orders_2(A_172))
      | ~ r1_orders_2(A_172,A_170,A_171)
      | ~ r1_orders_2(A_172,A_171,A_170)
      | ~ m1_subset_1(A_170,u1_struct_0(A_172))
      | v1_xboole_0(u1_struct_0(A_172))
      | ~ m1_subset_1(A_171,u1_struct_0(A_172))
      | ~ v5_orders_2(A_172)
      | ~ l1_orders_2(A_172) ) ),
    inference(resolution,[status(thm)],[c_28,c_349])).

tff(c_371,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_365])).

tff(c_378,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_44,c_42,c_40,c_371])).

tff(c_379,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_378])).

tff(c_384,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_379])).

tff(c_387,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_384])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_387])).

tff(c_392,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_379])).

tff(c_12,plain,(
    ! [C_15,B_13,A_12] :
      ( v1_xboole_0(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(B_13,A_12)))
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    ! [A_69] :
      ( v1_xboole_0(u1_orders_2(A_69))
      | ~ v1_xboole_0(u1_struct_0(A_69))
      | ~ l1_orders_2(A_69) ) ),
    inference(resolution,[status(thm)],[c_90,c_12])).

tff(c_396,plain,
    ( v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_392,c_97])).

tff(c_402,plain,(
    v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_396])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.89/1.39  
% 2.89/1.39  %Foreground sorts:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Background operators:
% 2.89/1.39  
% 2.89/1.39  
% 2.89/1.39  %Foreground operators:
% 2.89/1.39  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.89/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.89/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.89/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.89/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.39  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.89/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.39  
% 2.89/1.41  tff(f_108, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 2.89/1.41  tff(f_87, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.89/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.89/1.41  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.89/1.41  tff(f_91, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.89/1.41  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.89/1.41  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 2.89/1.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.89/1.41  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 2.89/1.41  tff(f_53, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.89/1.41  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_38, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_120, plain, (![B_80, C_81, A_82]: (r2_hidden(k4_tarski(B_80, C_81), u1_orders_2(A_82)) | ~r1_orders_2(A_82, B_80, C_81) | ~m1_subset_1(C_81, u1_struct_0(A_82)) | ~m1_subset_1(B_80, u1_struct_0(A_82)) | ~l1_orders_2(A_82))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.89/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.41  tff(c_144, plain, (![A_86, B_87, C_88]: (~v1_xboole_0(u1_orders_2(A_86)) | ~r1_orders_2(A_86, B_87, C_88) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86))), inference(resolution, [status(thm)], [c_120, c_2])).
% 2.89/1.41  tff(c_146, plain, (~v1_xboole_0(u1_orders_2('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_38, c_144])).
% 2.89/1.41  tff(c_151, plain, (~v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_44, c_146])).
% 2.89/1.41  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.89/1.41  tff(c_90, plain, (![A_69]: (m1_subset_1(u1_orders_2(A_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_69), u1_struct_0(A_69)))) | ~l1_orders_2(A_69))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.89/1.41  tff(c_8, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.89/1.41  tff(c_96, plain, (![A_69]: (v1_relat_1(u1_orders_2(A_69)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_69), u1_struct_0(A_69))) | ~l1_orders_2(A_69))), inference(resolution, [status(thm)], [c_90, c_8])).
% 2.89/1.41  tff(c_100, plain, (![A_69]: (v1_relat_1(u1_orders_2(A_69)) | ~l1_orders_2(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 2.89/1.41  tff(c_36, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_40, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.89/1.41  tff(c_28, plain, (![A_33]: (r4_relat_2(u1_orders_2(A_33), u1_struct_0(A_33)) | ~v5_orders_2(A_33) | ~l1_orders_2(A_33))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.41  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.41  tff(c_32, plain, (![B_38, C_40, A_34]: (r2_hidden(k4_tarski(B_38, C_40), u1_orders_2(A_34)) | ~r1_orders_2(A_34, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.89/1.41  tff(c_155, plain, (![D_89, C_90, A_91, B_92]: (D_89=C_90 | ~r2_hidden(k4_tarski(D_89, C_90), A_91) | ~r2_hidden(k4_tarski(C_90, D_89), A_91) | ~r2_hidden(D_89, B_92) | ~r2_hidden(C_90, B_92) | ~r4_relat_2(A_91, B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.89/1.41  tff(c_287, plain, (![C_146, B_147, A_148, B_149]: (C_146=B_147 | ~r2_hidden(k4_tarski(C_146, B_147), u1_orders_2(A_148)) | ~r2_hidden(B_147, B_149) | ~r2_hidden(C_146, B_149) | ~r4_relat_2(u1_orders_2(A_148), B_149) | ~v1_relat_1(u1_orders_2(A_148)) | ~r1_orders_2(A_148, B_147, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_148)) | ~m1_subset_1(B_147, u1_struct_0(A_148)) | ~l1_orders_2(A_148))), inference(resolution, [status(thm)], [c_32, c_155])).
% 2.89/1.41  tff(c_303, plain, (![C_150, B_151, B_152, A_153]: (C_150=B_151 | ~r2_hidden(C_150, B_152) | ~r2_hidden(B_151, B_152) | ~r4_relat_2(u1_orders_2(A_153), B_152) | ~v1_relat_1(u1_orders_2(A_153)) | ~r1_orders_2(A_153, C_150, B_151) | ~r1_orders_2(A_153, B_151, C_150) | ~m1_subset_1(C_150, u1_struct_0(A_153)) | ~m1_subset_1(B_151, u1_struct_0(A_153)) | ~l1_orders_2(A_153))), inference(resolution, [status(thm)], [c_32, c_287])).
% 2.89/1.41  tff(c_325, plain, (![B_154, A_155, B_156, A_157]: (B_154=A_155 | ~r2_hidden(B_154, B_156) | ~r4_relat_2(u1_orders_2(A_157), B_156) | ~v1_relat_1(u1_orders_2(A_157)) | ~r1_orders_2(A_157, A_155, B_154) | ~r1_orders_2(A_157, B_154, A_155) | ~m1_subset_1(A_155, u1_struct_0(A_157)) | ~m1_subset_1(B_154, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | v1_xboole_0(B_156) | ~m1_subset_1(A_155, B_156))), inference(resolution, [status(thm)], [c_6, c_303])).
% 2.89/1.41  tff(c_349, plain, (![A_167, A_166, A_168, B_169]: (A_167=A_166 | ~r4_relat_2(u1_orders_2(A_168), B_169) | ~v1_relat_1(u1_orders_2(A_168)) | ~r1_orders_2(A_168, A_167, A_166) | ~r1_orders_2(A_168, A_166, A_167) | ~m1_subset_1(A_167, u1_struct_0(A_168)) | ~m1_subset_1(A_166, u1_struct_0(A_168)) | ~l1_orders_2(A_168) | ~m1_subset_1(A_167, B_169) | v1_xboole_0(B_169) | ~m1_subset_1(A_166, B_169))), inference(resolution, [status(thm)], [c_6, c_325])).
% 2.89/1.41  tff(c_365, plain, (![A_171, A_170, A_172]: (A_171=A_170 | ~v1_relat_1(u1_orders_2(A_172)) | ~r1_orders_2(A_172, A_170, A_171) | ~r1_orders_2(A_172, A_171, A_170) | ~m1_subset_1(A_170, u1_struct_0(A_172)) | v1_xboole_0(u1_struct_0(A_172)) | ~m1_subset_1(A_171, u1_struct_0(A_172)) | ~v5_orders_2(A_172) | ~l1_orders_2(A_172))), inference(resolution, [status(thm)], [c_28, c_349])).
% 2.89/1.41  tff(c_371, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_38, c_365])).
% 2.89/1.41  tff(c_378, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_44, c_42, c_40, c_371])).
% 2.89/1.41  tff(c_379, plain, (~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_36, c_378])).
% 2.89/1.41  tff(c_384, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_379])).
% 2.89/1.41  tff(c_387, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_100, c_384])).
% 2.89/1.41  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_387])).
% 2.89/1.41  tff(c_392, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_379])).
% 2.89/1.41  tff(c_12, plain, (![C_15, B_13, A_12]: (v1_xboole_0(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(B_13, A_12))) | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.41  tff(c_97, plain, (![A_69]: (v1_xboole_0(u1_orders_2(A_69)) | ~v1_xboole_0(u1_struct_0(A_69)) | ~l1_orders_2(A_69))), inference(resolution, [status(thm)], [c_90, c_12])).
% 2.89/1.41  tff(c_396, plain, (v1_xboole_0(u1_orders_2('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_392, c_97])).
% 2.89/1.41  tff(c_402, plain, (v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_396])).
% 2.89/1.41  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_402])).
% 2.89/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  Inference rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Ref     : 0
% 2.89/1.41  #Sup     : 83
% 2.89/1.41  #Fact    : 0
% 2.89/1.41  #Define  : 0
% 2.89/1.41  #Split   : 1
% 2.89/1.41  #Chain   : 0
% 2.89/1.41  #Close   : 0
% 2.89/1.41  
% 2.89/1.41  Ordering : KBO
% 2.89/1.41  
% 2.89/1.41  Simplification rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Subsume      : 13
% 2.89/1.41  #Demod        : 19
% 2.89/1.41  #Tautology    : 9
% 2.89/1.41  #SimpNegUnit  : 3
% 2.89/1.41  #BackRed      : 0
% 2.89/1.41  
% 2.89/1.41  #Partial instantiations: 0
% 2.89/1.41  #Strategies tried      : 1
% 2.89/1.41  
% 2.89/1.41  Timing (in seconds)
% 2.89/1.41  ----------------------
% 2.89/1.41  Preprocessing        : 0.31
% 2.89/1.41  Parsing              : 0.16
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.34
% 2.89/1.41  Inferencing          : 0.13
% 2.89/1.41  Reduction            : 0.08
% 2.89/1.41  Demodulation         : 0.05
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.08
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.68
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
