%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:19 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 295 expanded)
%              Number of equality atoms :   15 (  28 expanded)
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

tff(f_105,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v5_orders_2(A)
      <=> r4_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_orders_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_66,axiom,(
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

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_95,plain,(
    ! [A_59] :
      ( m1_subset_1(u1_orders_2(A_59),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_59),u1_struct_0(A_59))))
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [A_59] :
      ( v1_relat_1(u1_orders_2(A_59))
      | ~ l1_orders_2(A_59) ) ),
    inference(resolution,[status(thm)],[c_95,c_12])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_51,plain,(
    ! [B_42,A_43] :
      ( v1_xboole_0(B_42)
      | ~ m1_subset_1(B_42,A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_62,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_64,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_48,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    r1_orders_2('#skF_3','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [A_25] :
      ( r4_relat_2(u1_orders_2(A_25),u1_struct_0(A_25))
      | ~ v5_orders_2(A_25)
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r2_hidden(B_4,A_3)
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [B_30,C_32,A_26] :
      ( r2_hidden(k4_tarski(B_30,C_32),u1_orders_2(A_26))
      | ~ r1_orders_2(A_26,B_30,C_32)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_195,plain,(
    ! [D_88,C_89,A_90,B_91] :
      ( D_88 = C_89
      | ~ r2_hidden(k4_tarski(D_88,C_89),A_90)
      | ~ r2_hidden(k4_tarski(C_89,D_88),A_90)
      | ~ r2_hidden(D_88,B_91)
      | ~ r2_hidden(C_89,B_91)
      | ~ r4_relat_2(A_90,B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_376,plain,(
    ! [C_148,B_149,A_150,B_151] :
      ( C_148 = B_149
      | ~ r2_hidden(k4_tarski(C_148,B_149),u1_orders_2(A_150))
      | ~ r2_hidden(B_149,B_151)
      | ~ r2_hidden(C_148,B_151)
      | ~ r4_relat_2(u1_orders_2(A_150),B_151)
      | ~ v1_relat_1(u1_orders_2(A_150))
      | ~ r1_orders_2(A_150,B_149,C_148)
      | ~ m1_subset_1(C_148,u1_struct_0(A_150))
      | ~ m1_subset_1(B_149,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(resolution,[status(thm)],[c_32,c_195])).

tff(c_392,plain,(
    ! [C_152,B_153,B_154,A_155] :
      ( C_152 = B_153
      | ~ r2_hidden(C_152,B_154)
      | ~ r2_hidden(B_153,B_154)
      | ~ r4_relat_2(u1_orders_2(A_155),B_154)
      | ~ v1_relat_1(u1_orders_2(A_155))
      | ~ r1_orders_2(A_155,C_152,B_153)
      | ~ r1_orders_2(A_155,B_153,C_152)
      | ~ m1_subset_1(C_152,u1_struct_0(A_155))
      | ~ m1_subset_1(B_153,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(resolution,[status(thm)],[c_32,c_376])).

tff(c_411,plain,(
    ! [B_157,B_156,A_158,A_159] :
      ( B_157 = B_156
      | ~ r2_hidden(B_157,A_158)
      | ~ r4_relat_2(u1_orders_2(A_159),A_158)
      | ~ v1_relat_1(u1_orders_2(A_159))
      | ~ r1_orders_2(A_159,B_156,B_157)
      | ~ r1_orders_2(A_159,B_157,B_156)
      | ~ m1_subset_1(B_156,u1_struct_0(A_159))
      | ~ m1_subset_1(B_157,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159)
      | ~ m1_subset_1(B_156,A_158)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_6,c_392])).

tff(c_454,plain,(
    ! [B_169,B_168,A_170,A_171] :
      ( B_169 = B_168
      | ~ r4_relat_2(u1_orders_2(A_170),A_171)
      | ~ v1_relat_1(u1_orders_2(A_170))
      | ~ r1_orders_2(A_170,B_169,B_168)
      | ~ r1_orders_2(A_170,B_168,B_169)
      | ~ m1_subset_1(B_169,u1_struct_0(A_170))
      | ~ m1_subset_1(B_168,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ m1_subset_1(B_169,A_171)
      | ~ m1_subset_1(B_168,A_171)
      | v1_xboole_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_6,c_411])).

tff(c_462,plain,(
    ! [B_173,B_172,A_174] :
      ( B_173 = B_172
      | ~ v1_relat_1(u1_orders_2(A_174))
      | ~ r1_orders_2(A_174,B_172,B_173)
      | ~ r1_orders_2(A_174,B_173,B_172)
      | ~ m1_subset_1(B_172,u1_struct_0(A_174))
      | ~ m1_subset_1(B_173,u1_struct_0(A_174))
      | v1_xboole_0(u1_struct_0(A_174))
      | ~ v5_orders_2(A_174)
      | ~ l1_orders_2(A_174) ) ),
    inference(resolution,[status(thm)],[c_28,c_454])).

tff(c_468,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | ~ r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v5_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_462])).

tff(c_475,plain,
    ( '#skF_5' = '#skF_4'
    | ~ v1_relat_1(u1_orders_2('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_44,c_42,c_40,c_468])).

tff(c_476,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_36,c_475])).

tff(c_483,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_476])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_483])).

tff(c_489,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_497,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_63])).

tff(c_488,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_501,plain,(
    ! [A_175] :
      ( A_175 = '#skF_4'
      | ~ v1_xboole_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_488,c_2])).

tff(c_504,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_497,c_501])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  %$ r1_orders_2 > r4_relat_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.49  
% 3.26/1.49  %Foreground sorts:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Background operators:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Foreground operators:
% 3.26/1.49  tff(r4_relat_2, type, r4_relat_2: ($i * $i) > $o).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.26/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.26/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.49  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.26/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.49  
% 3.37/1.50  tff(f_105, negated_conjecture, ~(![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 3.37/1.50  tff(f_88, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 3.37/1.50  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.37/1.50  tff(f_46, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.37/1.50  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (v5_orders_2(A) <=> r4_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_orders_2)).
% 3.37/1.50  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 3.37/1.50  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (r4_relat_2(A, B) <=> (![C, D]: ((((r2_hidden(C, B) & r2_hidden(D, B)) & r2_hidden(k4_tarski(C, D), A)) & r2_hidden(k4_tarski(D, C), A)) => (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_2)).
% 3.37/1.50  tff(f_33, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.37/1.50  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_46, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_95, plain, (![A_59]: (m1_subset_1(u1_orders_2(A_59), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_59), u1_struct_0(A_59)))) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.37/1.50  tff(c_12, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.50  tff(c_102, plain, (![A_59]: (v1_relat_1(u1_orders_2(A_59)) | ~l1_orders_2(A_59))), inference(resolution, [status(thm)], [c_95, c_12])).
% 3.37/1.50  tff(c_44, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_51, plain, (![B_42, A_43]: (v1_xboole_0(B_42) | ~m1_subset_1(B_42, A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.50  tff(c_62, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_51])).
% 3.37/1.50  tff(c_64, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.37/1.50  tff(c_48, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_40, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_38, plain, (r1_orders_2('#skF_3', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.37/1.50  tff(c_28, plain, (![A_25]: (r4_relat_2(u1_orders_2(A_25), u1_struct_0(A_25)) | ~v5_orders_2(A_25) | ~l1_orders_2(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.37/1.50  tff(c_6, plain, (![B_4, A_3]: (r2_hidden(B_4, A_3) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.50  tff(c_32, plain, (![B_30, C_32, A_26]: (r2_hidden(k4_tarski(B_30, C_32), u1_orders_2(A_26)) | ~r1_orders_2(A_26, B_30, C_32) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.37/1.50  tff(c_195, plain, (![D_88, C_89, A_90, B_91]: (D_88=C_89 | ~r2_hidden(k4_tarski(D_88, C_89), A_90) | ~r2_hidden(k4_tarski(C_89, D_88), A_90) | ~r2_hidden(D_88, B_91) | ~r2_hidden(C_89, B_91) | ~r4_relat_2(A_90, B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.37/1.50  tff(c_376, plain, (![C_148, B_149, A_150, B_151]: (C_148=B_149 | ~r2_hidden(k4_tarski(C_148, B_149), u1_orders_2(A_150)) | ~r2_hidden(B_149, B_151) | ~r2_hidden(C_148, B_151) | ~r4_relat_2(u1_orders_2(A_150), B_151) | ~v1_relat_1(u1_orders_2(A_150)) | ~r1_orders_2(A_150, B_149, C_148) | ~m1_subset_1(C_148, u1_struct_0(A_150)) | ~m1_subset_1(B_149, u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(resolution, [status(thm)], [c_32, c_195])).
% 3.37/1.50  tff(c_392, plain, (![C_152, B_153, B_154, A_155]: (C_152=B_153 | ~r2_hidden(C_152, B_154) | ~r2_hidden(B_153, B_154) | ~r4_relat_2(u1_orders_2(A_155), B_154) | ~v1_relat_1(u1_orders_2(A_155)) | ~r1_orders_2(A_155, C_152, B_153) | ~r1_orders_2(A_155, B_153, C_152) | ~m1_subset_1(C_152, u1_struct_0(A_155)) | ~m1_subset_1(B_153, u1_struct_0(A_155)) | ~l1_orders_2(A_155))), inference(resolution, [status(thm)], [c_32, c_376])).
% 3.37/1.50  tff(c_411, plain, (![B_157, B_156, A_158, A_159]: (B_157=B_156 | ~r2_hidden(B_157, A_158) | ~r4_relat_2(u1_orders_2(A_159), A_158) | ~v1_relat_1(u1_orders_2(A_159)) | ~r1_orders_2(A_159, B_156, B_157) | ~r1_orders_2(A_159, B_157, B_156) | ~m1_subset_1(B_156, u1_struct_0(A_159)) | ~m1_subset_1(B_157, u1_struct_0(A_159)) | ~l1_orders_2(A_159) | ~m1_subset_1(B_156, A_158) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_6, c_392])).
% 3.37/1.50  tff(c_454, plain, (![B_169, B_168, A_170, A_171]: (B_169=B_168 | ~r4_relat_2(u1_orders_2(A_170), A_171) | ~v1_relat_1(u1_orders_2(A_170)) | ~r1_orders_2(A_170, B_169, B_168) | ~r1_orders_2(A_170, B_168, B_169) | ~m1_subset_1(B_169, u1_struct_0(A_170)) | ~m1_subset_1(B_168, u1_struct_0(A_170)) | ~l1_orders_2(A_170) | ~m1_subset_1(B_169, A_171) | ~m1_subset_1(B_168, A_171) | v1_xboole_0(A_171))), inference(resolution, [status(thm)], [c_6, c_411])).
% 3.37/1.50  tff(c_462, plain, (![B_173, B_172, A_174]: (B_173=B_172 | ~v1_relat_1(u1_orders_2(A_174)) | ~r1_orders_2(A_174, B_172, B_173) | ~r1_orders_2(A_174, B_173, B_172) | ~m1_subset_1(B_172, u1_struct_0(A_174)) | ~m1_subset_1(B_173, u1_struct_0(A_174)) | v1_xboole_0(u1_struct_0(A_174)) | ~v5_orders_2(A_174) | ~l1_orders_2(A_174))), inference(resolution, [status(thm)], [c_28, c_454])).
% 3.37/1.50  tff(c_468, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | ~r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~v5_orders_2('#skF_3') | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_38, c_462])).
% 3.37/1.50  tff(c_475, plain, ('#skF_5'='#skF_4' | ~v1_relat_1(u1_orders_2('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_44, c_42, c_40, c_468])).
% 3.37/1.50  tff(c_476, plain, (~v1_relat_1(u1_orders_2('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_36, c_475])).
% 3.37/1.50  tff(c_483, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_102, c_476])).
% 3.37/1.50  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_483])).
% 3.37/1.50  tff(c_489, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 3.37/1.50  tff(c_63, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_51])).
% 3.37/1.50  tff(c_497, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_63])).
% 3.37/1.50  tff(c_488, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_62])).
% 3.37/1.50  tff(c_2, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.37/1.50  tff(c_501, plain, (![A_175]: (A_175='#skF_4' | ~v1_xboole_0(A_175))), inference(resolution, [status(thm)], [c_488, c_2])).
% 3.37/1.50  tff(c_504, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_497, c_501])).
% 3.37/1.50  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_504])).
% 3.37/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.50  
% 3.37/1.50  Inference rules
% 3.37/1.50  ----------------------
% 3.37/1.50  #Ref     : 0
% 3.37/1.50  #Sup     : 107
% 3.37/1.50  #Fact    : 0
% 3.37/1.50  #Define  : 0
% 3.37/1.50  #Split   : 2
% 3.37/1.50  #Chain   : 0
% 3.37/1.50  #Close   : 0
% 3.37/1.50  
% 3.37/1.50  Ordering : KBO
% 3.37/1.50  
% 3.37/1.50  Simplification rules
% 3.37/1.50  ----------------------
% 3.37/1.50  #Subsume      : 10
% 3.37/1.50  #Demod        : 12
% 3.37/1.50  #Tautology    : 24
% 3.37/1.50  #SimpNegUnit  : 7
% 3.37/1.50  #BackRed      : 0
% 3.37/1.50  
% 3.37/1.50  #Partial instantiations: 0
% 3.37/1.50  #Strategies tried      : 1
% 3.37/1.50  
% 3.37/1.50  Timing (in seconds)
% 3.37/1.50  ----------------------
% 3.37/1.50  Preprocessing        : 0.32
% 3.37/1.50  Parsing              : 0.17
% 3.37/1.50  CNF conversion       : 0.02
% 3.37/1.50  Main loop            : 0.38
% 3.37/1.50  Inferencing          : 0.14
% 3.37/1.50  Reduction            : 0.08
% 3.37/1.50  Demodulation         : 0.05
% 3.37/1.50  BG Simplification    : 0.02
% 3.37/1.50  Subsumption          : 0.10
% 3.37/1.50  Abstraction          : 0.02
% 3.37/1.50  MUC search           : 0.00
% 3.37/1.50  Cooper               : 0.00
% 3.37/1.50  Total                : 0.73
% 3.37/1.50  Index Insertion      : 0.00
% 3.37/1.50  Index Deletion       : 0.00
% 3.37/1.50  Index Matching       : 0.00
% 3.37/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
