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

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 126 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 ( 447 expanded)
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

tff(f_103,negated_conjecture,(
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

tff(f_82,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
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

tff(f_64,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_115,plain,(
    ! [B_77,C_78,A_79] :
      ( r2_hidden(k4_tarski(B_77,C_78),u1_orders_2(A_79))
      | ~ r1_orders_2(A_79,B_77,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_79))
      | ~ m1_subset_1(B_77,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ v1_xboole_0(u1_orders_2(A_83))
      | ~ r1_orders_2(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ m1_subset_1(B_84,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_141,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_139])).

tff(c_146,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_141])).

tff(c_87,plain,(
    ! [A_66] :
      ( m1_subset_1(u1_orders_2(A_66),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66),u1_struct_0(A_66))))
      | ~ l1_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_66] :
      ( v1_relat_1(u1_orders_2(A_66))
      | ~ l1_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_87,c_8])).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    ! [A_31] :
      ( r4_relat_2(u1_orders_2(A_31),u1_struct_0(A_31))
      | ~ v5_orders_2(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [B_36,C_38,A_32] :
      ( r2_hidden(k4_tarski(B_36,C_38),u1_orders_2(A_32))
      | ~ r1_orders_2(A_32,B_36,C_38)
      | ~ m1_subset_1(C_38,u1_struct_0(A_32))
      | ~ m1_subset_1(B_36,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_150,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_hidden(k4_tarski(D_86,C_87),A_88)
      | ~ r2_hidden(k4_tarski(C_87,D_86),A_88)
      | ~ r2_hidden(D_86,B_89)
      | ~ r2_hidden(C_87,B_89)
      | ~ r4_relat_2(A_88,B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_282,plain,(
    ! [C_143,B_144,A_145,B_146] :
      ( C_143 = B_144
      | ~ r2_hidden(k4_tarski(C_143,B_144),u1_orders_2(A_145))
      | ~ r2_hidden(B_144,B_146)
      | ~ r2_hidden(C_143,B_146)
      | ~ r4_relat_2(u1_orders_2(A_145),B_146)
      | ~ v1_relat_1(u1_orders_2(A_145))
      | ~ r1_orders_2(A_145,B_144,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(A_145))
      | ~ m1_subset_1(B_144,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145) ) ),
    inference(resolution,[status(thm)],[c_30,c_150])).

tff(c_298,plain,(
    ! [C_147,B_148,B_149,A_150] :
      ( C_147 = B_148
      | ~ r2_hidden(C_147,B_149)
      | ~ r2_hidden(B_148,B_149)
      | ~ r4_relat_2(u1_orders_2(A_150),B_149)
      | ~ v1_relat_1(u1_orders_2(A_150))
      | ~ r1_orders_2(A_150,C_147,B_148)
      | ~ r1_orders_2(A_150,B_148,C_147)
      | ~ m1_subset_1(C_147,u1_struct_0(A_150))
      | ~ m1_subset_1(B_148,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(resolution,[status(thm)],[c_30,c_282])).

tff(c_320,plain,(
    ! [B_151,A_152,B_153,A_154] :
      ( B_151 = A_152
      | ~ r2_hidden(B_151,B_153)
      | ~ r4_relat_2(u1_orders_2(A_154),B_153)
      | ~ v1_relat_1(u1_orders_2(A_154))
      | ~ r1_orders_2(A_154,A_152,B_151)
      | ~ r1_orders_2(A_154,B_151,A_152)
      | ~ m1_subset_1(A_152,u1_struct_0(A_154))
      | ~ m1_subset_1(B_151,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154)
      | v1_xboole_0(B_153)
      | ~ m1_subset_1(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_6,c_298])).

tff(c_344,plain,(
    ! [A_164,A_163,A_165,B_166] :
      ( A_164 = A_163
      | ~ r4_relat_2(u1_orders_2(A_165),B_166)
      | ~ v1_relat_1(u1_orders_2(A_165))
      | ~ r1_orders_2(A_165,A_164,A_163)
      | ~ r1_orders_2(A_165,A_163,A_164)
      | ~ m1_subset_1(A_164,u1_struct_0(A_165))
      | ~ m1_subset_1(A_163,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ m1_subset_1(A_164,B_166)
      | v1_xboole_0(B_166)
      | ~ m1_subset_1(A_163,B_166) ) ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_360,plain,(
    ! [A_168,A_167,A_169] :
      ( A_168 = A_167
      | ~ v1_relat_1(u1_orders_2(A_169))
      | ~ r1_orders_2(A_169,A_167,A_168)
      | ~ r1_orders_2(A_169,A_168,A_167)
      | ~ m1_subset_1(A_167,u1_struct_0(A_169))
      | v1_xboole_0(u1_struct_0(A_169))
      | ~ m1_subset_1(A_168,u1_struct_0(A_169))
      | ~ v5_orders_2(A_169)
      | ~ l1_orders_2(A_169) ) ),
    inference(resolution,[status(thm)],[c_26,c_344])).

tff(c_366,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_360])).

tff(c_373,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_40,c_38,c_366])).

tff(c_374,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_373])).

tff(c_379,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_382,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_379])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_382])).

tff(c_387,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_10,plain,(
    ! [C_13,B_11,A_10] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(B_11,A_10)))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [A_66] :
      ( v1_xboole_0(u1_orders_2(A_66))
      | ~ v1_xboole_0(u1_struct_0(A_66))
      | ~ l1_orders_2(A_66) ) ),
    inference(resolution,[status(thm)],[c_87,c_10])).

tff(c_391,plain,
    ( v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_387,c_94])).

tff(c_397,plain,(
    v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_391])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.40  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.83/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.40  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.83/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.40  
% 2.83/1.41  tff(f_103, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 2.83/1.41  tff(f_82, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.83/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.83/1.41  tff(f_86, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.83/1.41  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.41  tff(f_70, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 2.83/1.41  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.83/1.41  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 2.83/1.41  tff(f_48, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.83/1.41  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_36, plain, (r1_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_115, plain, (![B_77, C_78, A_79]: (r2_hidden(k4_tarski(B_77, C_78), u1_orders_2(A_79)) | ~r1_orders_2(A_79, B_77, C_78) | ~m1_subset_1(C_78, u1_struct_0(A_79)) | ~m1_subset_1(B_77, u1_struct_0(A_79)) | ~l1_orders_2(A_79))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.83/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.41  tff(c_139, plain, (![A_83, B_84, C_85]: (~v1_xboole_0(u1_orders_2(A_83)) | ~r1_orders_2(A_83, B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~m1_subset_1(B_84, u1_struct_0(A_83)) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_115, c_2])).
% 2.83/1.41  tff(c_141, plain, (~v1_xboole_0(u1_orders_2('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_36, c_139])).
% 2.83/1.41  tff(c_146, plain, (~v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_141])).
% 2.83/1.41  tff(c_87, plain, (![A_66]: (m1_subset_1(u1_orders_2(A_66), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_66), u1_struct_0(A_66)))) | ~l1_orders_2(A_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.41  tff(c_8, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.83/1.41  tff(c_95, plain, (![A_66]: (v1_relat_1(u1_orders_2(A_66)) | ~l1_orders_2(A_66))), inference(resolution, [status(thm)], [c_87, c_8])).
% 2.83/1.41  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_38, plain, (r1_orders_2('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.41  tff(c_26, plain, (![A_31]: (r4_relat_2(u1_orders_2(A_31), u1_struct_0(A_31)) | ~v5_orders_2(A_31) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.83/1.41  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.83/1.41  tff(c_30, plain, (![B_36, C_38, A_32]: (r2_hidden(k4_tarski(B_36, C_38), u1_orders_2(A_32)) | ~r1_orders_2(A_32, B_36, C_38) | ~m1_subset_1(C_38, u1_struct_0(A_32)) | ~m1_subset_1(B_36, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.83/1.41  tff(c_150, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_hidden(k4_tarski(D_86, C_87), A_88) | ~r2_hidden(k4_tarski(C_87, D_86), A_88) | ~r2_hidden(D_86, B_89) | ~r2_hidden(C_87, B_89) | ~r4_relat_2(A_88, B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.41  tff(c_282, plain, (![C_143, B_144, A_145, B_146]: (C_143=B_144 | ~r2_hidden(k4_tarski(C_143, B_144), u1_orders_2(A_145)) | ~r2_hidden(B_144, B_146) | ~r2_hidden(C_143, B_146) | ~r4_relat_2(u1_orders_2(A_145), B_146) | ~v1_relat_1(u1_orders_2(A_145)) | ~r1_orders_2(A_145, B_144, C_143) | ~m1_subset_1(C_143, u1_struct_0(A_145)) | ~m1_subset_1(B_144, u1_struct_0(A_145)) | ~l1_orders_2(A_145))), inference(resolution, [status(thm)], [c_30, c_150])).
% 2.83/1.41  tff(c_298, plain, (![C_147, B_148, B_149, A_150]: (C_147=B_148 | ~r2_hidden(C_147, B_149) | ~r2_hidden(B_148, B_149) | ~r4_relat_2(u1_orders_2(A_150), B_149) | ~v1_relat_1(u1_orders_2(A_150)) | ~r1_orders_2(A_150, C_147, B_148) | ~r1_orders_2(A_150, B_148, C_147) | ~m1_subset_1(C_147, u1_struct_0(A_150)) | ~m1_subset_1(B_148, u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(resolution, [status(thm)], [c_30, c_282])).
% 2.83/1.41  tff(c_320, plain, (![B_151, A_152, B_153, A_154]: (B_151=A_152 | ~r2_hidden(B_151, B_153) | ~r4_relat_2(u1_orders_2(A_154), B_153) | ~v1_relat_1(u1_orders_2(A_154)) | ~r1_orders_2(A_154, A_152, B_151) | ~r1_orders_2(A_154, B_151, A_152) | ~m1_subset_1(A_152, u1_struct_0(A_154)) | ~m1_subset_1(B_151, u1_struct_0(A_154)) | ~l1_orders_2(A_154) | v1_xboole_0(B_153) | ~m1_subset_1(A_152, B_153))), inference(resolution, [status(thm)], [c_6, c_298])).
% 2.83/1.41  tff(c_344, plain, (![A_164, A_163, A_165, B_166]: (A_164=A_163 | ~r4_relat_2(u1_orders_2(A_165), B_166) | ~v1_relat_1(u1_orders_2(A_165)) | ~r1_orders_2(A_165, A_164, A_163) | ~r1_orders_2(A_165, A_163, A_164) | ~m1_subset_1(A_164, u1_struct_0(A_165)) | ~m1_subset_1(A_163, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~m1_subset_1(A_164, B_166) | v1_xboole_0(B_166) | ~m1_subset_1(A_163, B_166))), inference(resolution, [status(thm)], [c_6, c_320])).
% 2.83/1.41  tff(c_360, plain, (![A_168, A_167, A_169]: (A_168=A_167 | ~v1_relat_1(u1_orders_2(A_169)) | ~r1_orders_2(A_169, A_167, A_168) | ~r1_orders_2(A_169, A_168, A_167) | ~m1_subset_1(A_167, u1_struct_0(A_169)) | v1_xboole_0(u1_struct_0(A_169)) | ~m1_subset_1(A_168, u1_struct_0(A_169)) | ~v5_orders_2(A_169) | ~l1_orders_2(A_169))), inference(resolution, [status(thm)], [c_26, c_344])).
% 2.83/1.41  tff(c_366, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | ~r1_orders_2('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_36, c_360])).
% 2.83/1.41  tff(c_373, plain, ('#skF_5'='#skF_6' | ~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_42, c_40, c_38, c_366])).
% 2.83/1.41  tff(c_374, plain, (~v1_relat_1(u1_orders_2('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_34, c_373])).
% 2.83/1.41  tff(c_379, plain, (~v1_relat_1(u1_orders_2('#skF_4'))), inference(splitLeft, [status(thm)], [c_374])).
% 2.83/1.41  tff(c_382, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_95, c_379])).
% 2.83/1.41  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_382])).
% 2.83/1.41  tff(c_387, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_374])).
% 2.83/1.41  tff(c_10, plain, (![C_13, B_11, A_10]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(B_11, A_10))) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.83/1.41  tff(c_94, plain, (![A_66]: (v1_xboole_0(u1_orders_2(A_66)) | ~v1_xboole_0(u1_struct_0(A_66)) | ~l1_orders_2(A_66))), inference(resolution, [status(thm)], [c_87, c_10])).
% 2.83/1.41  tff(c_391, plain, (v1_xboole_0(u1_orders_2('#skF_4')) | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_387, c_94])).
% 2.83/1.41  tff(c_397, plain, (v1_xboole_0(u1_orders_2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_391])).
% 2.83/1.41  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_397])).
% 2.83/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  Inference rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Ref     : 0
% 2.83/1.41  #Sup     : 83
% 2.83/1.41  #Fact    : 0
% 2.83/1.41  #Define  : 0
% 2.83/1.41  #Split   : 1
% 2.83/1.41  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 13
% 2.83/1.42  #Demod        : 18
% 2.83/1.42  #Tautology    : 9
% 2.83/1.42  #SimpNegUnit  : 3
% 2.83/1.42  #BackRed      : 0
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.42  Preprocessing        : 0.31
% 2.83/1.42  Parsing              : 0.17
% 2.83/1.42  CNF conversion       : 0.02
% 2.83/1.42  Main loop            : 0.34
% 2.83/1.42  Inferencing          : 0.13
% 2.83/1.42  Reduction            : 0.08
% 2.83/1.42  Demodulation         : 0.05
% 2.83/1.42  BG Simplification    : 0.02
% 2.83/1.42  Subsumption          : 0.08
% 2.83/1.42  Abstraction          : 0.02
% 2.83/1.42  MUC search           : 0.00
% 2.83/1.42  Cooper               : 0.00
% 2.83/1.42  Total                : 0.68
% 2.83/1.42  Index Insertion      : 0.00
% 2.83/1.42  Index Deletion       : 0.00
% 2.83/1.42  Index Matching       : 0.00
% 2.83/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
