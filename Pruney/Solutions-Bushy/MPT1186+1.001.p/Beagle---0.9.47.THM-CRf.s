%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1186+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:33 EST 2020

% Result     : Theorem 5.05s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  181 (1094 expanded)
%              Number of leaves         :   47 ( 407 expanded)
%              Depth                    :   23
%              Number of atoms          :  543 (4607 expanded)
%              Number of equality atoms :   51 ( 251 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > v1_partfun1 > r7_orders_1 > r2_hidden > m1_subset_1 > v8_relat_2 > v5_orders_2 > v4_relat_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_orders_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r7_orders_1,type,(
    r7_orders_1: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_orders_2,type,(
    v2_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_166,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r7_orders_1(u1_orders_2(A),B)
            <=> ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_orders_2)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_143,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
       => v2_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_orders_2)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & l1_orders_2(A) )
     => v1_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_orders_2)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => v4_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => v8_relat_2(u1_orders_2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_orders_2)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v2_orders_2(A)
        & l1_orders_2(A) )
     => v1_partfun1(u1_orders_2(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_orders_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_2(B)
        & v4_relat_2(B)
        & v8_relat_2(B)
        & v1_partfun1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k3_relat_1(B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_orders_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r7_orders_1(A,B)
        <=> ( r2_hidden(B,k3_relat_1(A))
            & ! [C] :
                ~ ( r2_hidden(C,k3_relat_1(A))
                  & C != B
                  & r2_hidden(k4_tarski(C,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_48,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_26,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | v1_xboole_0(B_41)
      | ~ m1_subset_1(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_54,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_71,plain,(
    ! [A_53] :
      ( v2_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_74,plain,
    ( v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_77,plain,(
    v2_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_74])).

tff(c_50,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_52,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    ! [A_33] :
      ( v1_relat_2(u1_orders_2(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [A_34] :
      ( v4_relat_2(u1_orders_2(A_34))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v2_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_35] :
      ( v8_relat_2(u1_orders_2(A_35))
      | ~ l1_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v2_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_31] :
      ( v1_partfun1(u1_orders_2(A_31),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v2_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_30] :
      ( m1_subset_1(u1_orders_2(A_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(A_30))))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_756,plain,(
    ! [B_208,A_209] :
      ( k3_relat_1(B_208) = A_209
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v1_partfun1(B_208,A_209)
      | ~ v8_relat_2(B_208)
      | ~ v4_relat_2(B_208)
      | ~ v1_relat_2(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_862,plain,(
    ! [A_235] :
      ( k3_relat_1(u1_orders_2(A_235)) = u1_struct_0(A_235)
      | ~ v1_partfun1(u1_orders_2(A_235),u1_struct_0(A_235))
      | ~ v8_relat_2(u1_orders_2(A_235))
      | ~ v4_relat_2(u1_orders_2(A_235))
      | ~ v1_relat_2(u1_orders_2(A_235))
      | ~ l1_orders_2(A_235) ) ),
    inference(resolution,[status(thm)],[c_28,c_756])).

tff(c_867,plain,(
    ! [A_236] :
      ( k3_relat_1(u1_orders_2(A_236)) = u1_struct_0(A_236)
      | ~ v8_relat_2(u1_orders_2(A_236))
      | ~ v4_relat_2(u1_orders_2(A_236))
      | ~ v1_relat_2(u1_orders_2(A_236))
      | ~ l1_orders_2(A_236)
      | ~ v2_orders_2(A_236) ) ),
    inference(resolution,[status(thm)],[c_30,c_862])).

tff(c_872,plain,(
    ! [A_237] :
      ( k3_relat_1(u1_orders_2(A_237)) = u1_struct_0(A_237)
      | ~ v4_relat_2(u1_orders_2(A_237))
      | ~ v1_relat_2(u1_orders_2(A_237))
      | ~ l1_orders_2(A_237)
      | ~ v4_orders_2(A_237)
      | ~ v2_orders_2(A_237) ) ),
    inference(resolution,[status(thm)],[c_38,c_867])).

tff(c_877,plain,(
    ! [A_238] :
      ( k3_relat_1(u1_orders_2(A_238)) = u1_struct_0(A_238)
      | ~ v1_relat_2(u1_orders_2(A_238))
      | ~ v4_orders_2(A_238)
      | ~ l1_orders_2(A_238)
      | ~ v5_orders_2(A_238)
      | ~ v2_orders_2(A_238) ) ),
    inference(resolution,[status(thm)],[c_36,c_872])).

tff(c_881,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_877])).

tff(c_60,plain,
    ( m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ r7_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_78,plain,(
    ~ r7_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_674,plain,(
    ! [A_188] :
      ( m1_subset_1(u1_orders_2(A_188),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(A_188))))
      | ~ l1_orders_2(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_678,plain,(
    ! [A_188] :
      ( v1_relat_1(u1_orders_2(A_188))
      | ~ l1_orders_2(A_188) ) ),
    inference(resolution,[status(thm)],[c_674,c_4])).

tff(c_882,plain,(
    ! [A_239] :
      ( k3_relat_1(u1_orders_2(A_239)) = u1_struct_0(A_239)
      | ~ v4_orders_2(A_239)
      | ~ v5_orders_2(A_239)
      | ~ v2_orders_2(A_239)
      | ~ l1_orders_2(A_239)
      | ~ v3_orders_2(A_239) ) ),
    inference(resolution,[status(thm)],[c_34,c_877])).

tff(c_18,plain,(
    ! [A_12,B_18] :
      ( '#skF_1'(A_12,B_18) != B_18
      | r7_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_978,plain,(
    ! [A_258,B_259] :
      ( '#skF_1'(u1_orders_2(A_258),B_259) != B_259
      | r7_orders_1(u1_orders_2(A_258),B_259)
      | ~ r2_hidden(B_259,u1_struct_0(A_258))
      | ~ v1_relat_1(u1_orders_2(A_258))
      | ~ v4_orders_2(A_258)
      | ~ v5_orders_2(A_258)
      | ~ v2_orders_2(A_258)
      | ~ l1_orders_2(A_258)
      | ~ v3_orders_2(A_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_18])).

tff(c_987,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_978,c_78])).

tff(c_992,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3'
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_987])).

tff(c_993,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_1015,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_678,c_993])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1015])).

tff(c_1020,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_1022,plain,(
    '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1020])).

tff(c_1021,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_690,plain,(
    ! [A_192,B_193] :
      ( r2_hidden('#skF_1'(A_192,B_193),k3_relat_1(A_192))
      | r7_orders_1(A_192,B_193)
      | ~ r2_hidden(B_193,k3_relat_1(A_192))
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(A_38,B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_698,plain,(
    ! [A_192,B_193] :
      ( m1_subset_1('#skF_1'(A_192,B_193),k3_relat_1(A_192))
      | r7_orders_1(A_192,B_193)
      | ~ r2_hidden(B_193,k3_relat_1(A_192))
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_690,c_42])).

tff(c_897,plain,(
    ! [A_239,B_193] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_239),B_193),u1_struct_0(A_239))
      | r7_orders_1(u1_orders_2(A_239),B_193)
      | ~ r2_hidden(B_193,k3_relat_1(u1_orders_2(A_239)))
      | ~ v1_relat_1(u1_orders_2(A_239))
      | ~ v4_orders_2(A_239)
      | ~ v5_orders_2(A_239)
      | ~ v2_orders_2(A_239)
      | ~ l1_orders_2(A_239)
      | ~ v3_orders_2(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_698])).

tff(c_16,plain,(
    ! [A_12,B_18] :
      ( r2_hidden(k4_tarski('#skF_1'(A_12,B_18),B_18),A_12)
      | r7_orders_1(A_12,B_18)
      | ~ r2_hidden(B_18,k3_relat_1(A_12))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_825,plain,(
    ! [A_223,B_224,C_225] :
      ( r1_orders_2(A_223,B_224,C_225)
      | ~ r2_hidden(k4_tarski(B_224,C_225),u1_orders_2(A_223))
      | ~ m1_subset_1(C_225,u1_struct_0(A_223))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_orders_2(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1069,plain,(
    ! [A_274,B_275] :
      ( r1_orders_2(A_274,'#skF_1'(u1_orders_2(A_274),B_275),B_275)
      | ~ m1_subset_1(B_275,u1_struct_0(A_274))
      | ~ m1_subset_1('#skF_1'(u1_orders_2(A_274),B_275),u1_struct_0(A_274))
      | ~ l1_orders_2(A_274)
      | r7_orders_1(u1_orders_2(A_274),B_275)
      | ~ r2_hidden(B_275,k3_relat_1(u1_orders_2(A_274)))
      | ~ v1_relat_1(u1_orders_2(A_274)) ) ),
    inference(resolution,[status(thm)],[c_16,c_825])).

tff(c_1188,plain,(
    ! [A_296,B_297] :
      ( r1_orders_2(A_296,'#skF_1'(u1_orders_2(A_296),B_297),B_297)
      | ~ m1_subset_1(B_297,u1_struct_0(A_296))
      | r7_orders_1(u1_orders_2(A_296),B_297)
      | ~ r2_hidden(B_297,k3_relat_1(u1_orders_2(A_296)))
      | ~ v1_relat_1(u1_orders_2(A_296))
      | ~ v4_orders_2(A_296)
      | ~ v5_orders_2(A_296)
      | ~ v2_orders_2(A_296)
      | ~ l1_orders_2(A_296)
      | ~ v3_orders_2(A_296) ) ),
    inference(resolution,[status(thm)],[c_897,c_1069])).

tff(c_1051,plain,(
    ! [A_272,B_273] :
      ( m1_subset_1('#skF_1'(u1_orders_2(A_272),B_273),u1_struct_0(A_272))
      | r7_orders_1(u1_orders_2(A_272),B_273)
      | ~ r2_hidden(B_273,k3_relat_1(u1_orders_2(A_272)))
      | ~ v1_relat_1(u1_orders_2(A_272))
      | ~ v4_orders_2(A_272)
      | ~ v5_orders_2(A_272)
      | ~ v2_orders_2(A_272)
      | ~ l1_orders_2(A_272)
      | ~ v3_orders_2(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_882,c_698])).

tff(c_802,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_orders_2(A_219,B_220,C_221)
      | C_221 = B_220
      | ~ r1_orders_2(A_219,B_220,C_221)
      | ~ m1_subset_1(C_221,u1_struct_0(A_219))
      | ~ m1_subset_1(B_220,u1_struct_0(A_219))
      | ~ l1_orders_2(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_807,plain,(
    ! [B_220] :
      ( r2_orders_2('#skF_2',B_220,'#skF_3')
      | B_220 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_220,'#skF_3')
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_802])).

tff(c_811,plain,(
    ! [B_220] :
      ( r2_orders_2('#skF_2',B_220,'#skF_3')
      | B_220 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_220,'#skF_3')
      | ~ m1_subset_1(B_220,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_807])).

tff(c_1055,plain,(
    ! [B_273] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_273),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_273) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_273),'#skF_3')
      | r7_orders_1(u1_orders_2('#skF_2'),B_273)
      | ~ r2_hidden(B_273,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1051,c_811])).

tff(c_1074,plain,(
    ! [B_277] :
      ( r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_277),'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),B_277) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_277),'#skF_3')
      | r7_orders_1(u1_orders_2('#skF_2'),B_277)
      | ~ r2_hidden(B_277,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1021,c_1055])).

tff(c_68,plain,(
    ! [C_49] :
      ( r7_orders_1(u1_orders_2('#skF_2'),'#skF_3')
      | ~ r2_orders_2('#skF_2',C_49,'#skF_3')
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_665,plain,(
    ! [C_49] :
      ( ~ r2_orders_2('#skF_2',C_49,'#skF_3')
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_68])).

tff(c_1061,plain,(
    ! [B_273] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_273),'#skF_3')
      | r7_orders_1(u1_orders_2('#skF_2'),B_273)
      | ~ r2_hidden(B_273,k3_relat_1(u1_orders_2('#skF_2')))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1051,c_665])).

tff(c_1068,plain,(
    ! [B_273] :
      ( ~ r2_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_273),'#skF_3')
      | r7_orders_1(u1_orders_2('#skF_2'),B_273)
      | ~ r2_hidden(B_273,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1021,c_1061])).

tff(c_1080,plain,(
    ! [B_277] :
      ( '#skF_1'(u1_orders_2('#skF_2'),B_277) = '#skF_3'
      | ~ r1_orders_2('#skF_2','#skF_1'(u1_orders_2('#skF_2'),B_277),'#skF_3')
      | r7_orders_1(u1_orders_2('#skF_2'),B_277)
      | ~ r2_hidden(B_277,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1074,c_1068])).

tff(c_1192,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | r7_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2')))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1188,c_1080])).

tff(c_1195,plain,
    ( '#skF_1'(u1_orders_2('#skF_2'),'#skF_3') = '#skF_3'
    | r7_orders_1(u1_orders_2('#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1021,c_46,c_1192])).

tff(c_1196,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1022,c_1195])).

tff(c_1199,plain,
    ( ~ r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_1196])).

tff(c_1207,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1199])).

tff(c_1216,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_1207])).

tff(c_1219,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1216])).

tff(c_32,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1222,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1219,c_32])).

tff(c_1225,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1222])).

tff(c_1228,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1225])).

tff(c_1232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1228])).

tff(c_1233,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1020])).

tff(c_1237,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_1233])).

tff(c_1240,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1237])).

tff(c_1243,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1240,c_32])).

tff(c_1246,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1243])).

tff(c_1268,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1246])).

tff(c_1272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1268])).

tff(c_1273,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1274,plain,(
    r7_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r2_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r7_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1275,plain,(
    ~ r7_orders_1(u1_orders_2('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_1277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1275])).

tff(c_1278,plain,(
    r2_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1383,plain,(
    ! [A_336,B_337,C_338] :
      ( r1_orders_2(A_336,B_337,C_338)
      | ~ r2_orders_2(A_336,B_337,C_338)
      | ~ m1_subset_1(C_338,u1_struct_0(A_336))
      | ~ m1_subset_1(B_337,u1_struct_0(A_336))
      | ~ l1_orders_2(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1385,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1278,c_1383])).

tff(c_1388,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1273,c_46,c_1385])).

tff(c_1353,plain,(
    ! [B_330,A_331] :
      ( k3_relat_1(B_330) = A_331
      | ~ m1_subset_1(B_330,k1_zfmisc_1(k2_zfmisc_1(A_331,A_331)))
      | ~ v1_partfun1(B_330,A_331)
      | ~ v8_relat_2(B_330)
      | ~ v4_relat_2(B_330)
      | ~ v1_relat_2(B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1491,plain,(
    ! [A_359] :
      ( k3_relat_1(u1_orders_2(A_359)) = u1_struct_0(A_359)
      | ~ v1_partfun1(u1_orders_2(A_359),u1_struct_0(A_359))
      | ~ v8_relat_2(u1_orders_2(A_359))
      | ~ v4_relat_2(u1_orders_2(A_359))
      | ~ v1_relat_2(u1_orders_2(A_359))
      | ~ l1_orders_2(A_359) ) ),
    inference(resolution,[status(thm)],[c_28,c_1353])).

tff(c_1496,plain,(
    ! [A_360] :
      ( k3_relat_1(u1_orders_2(A_360)) = u1_struct_0(A_360)
      | ~ v8_relat_2(u1_orders_2(A_360))
      | ~ v4_relat_2(u1_orders_2(A_360))
      | ~ v1_relat_2(u1_orders_2(A_360))
      | ~ l1_orders_2(A_360)
      | ~ v2_orders_2(A_360) ) ),
    inference(resolution,[status(thm)],[c_30,c_1491])).

tff(c_1501,plain,(
    ! [A_361] :
      ( k3_relat_1(u1_orders_2(A_361)) = u1_struct_0(A_361)
      | ~ v4_relat_2(u1_orders_2(A_361))
      | ~ v1_relat_2(u1_orders_2(A_361))
      | ~ l1_orders_2(A_361)
      | ~ v4_orders_2(A_361)
      | ~ v2_orders_2(A_361) ) ),
    inference(resolution,[status(thm)],[c_38,c_1496])).

tff(c_1523,plain,(
    ! [A_365] :
      ( k3_relat_1(u1_orders_2(A_365)) = u1_struct_0(A_365)
      | ~ v1_relat_2(u1_orders_2(A_365))
      | ~ v4_orders_2(A_365)
      | ~ l1_orders_2(A_365)
      | ~ v5_orders_2(A_365)
      | ~ v2_orders_2(A_365) ) ),
    inference(resolution,[status(thm)],[c_36,c_1501])).

tff(c_1527,plain,(
    ! [A_33] :
      ( k3_relat_1(u1_orders_2(A_33)) = u1_struct_0(A_33)
      | ~ v4_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v2_orders_2(A_33)
      | ~ l1_orders_2(A_33)
      | ~ v3_orders_2(A_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_1523])).

tff(c_1300,plain,(
    ! [A_317] :
      ( m1_subset_1(u1_orders_2(A_317),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_317),u1_struct_0(A_317))))
      | ~ l1_orders_2(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1304,plain,(
    ! [A_317] :
      ( v1_relat_1(u1_orders_2(A_317))
      | ~ l1_orders_2(A_317) ) ),
    inference(resolution,[status(thm)],[c_1300,c_4])).

tff(c_1528,plain,(
    ! [A_366] :
      ( k3_relat_1(u1_orders_2(A_366)) = u1_struct_0(A_366)
      | ~ v4_orders_2(A_366)
      | ~ v5_orders_2(A_366)
      | ~ v2_orders_2(A_366)
      | ~ l1_orders_2(A_366)
      | ~ v3_orders_2(A_366) ) ),
    inference(resolution,[status(thm)],[c_34,c_1523])).

tff(c_14,plain,(
    ! [B_18,A_12] :
      ( r2_hidden(B_18,k3_relat_1(A_12))
      | ~ r7_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1576,plain,(
    ! [B_373,A_374] :
      ( r2_hidden(B_373,u1_struct_0(A_374))
      | ~ r7_orders_1(u1_orders_2(A_374),B_373)
      | ~ v1_relat_1(u1_orders_2(A_374))
      | ~ v4_orders_2(A_374)
      | ~ v5_orders_2(A_374)
      | ~ v2_orders_2(A_374)
      | ~ l1_orders_2(A_374)
      | ~ v3_orders_2(A_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_14])).

tff(c_1579,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1274,c_1576])).

tff(c_1582,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1579])).

tff(c_1583,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1582])).

tff(c_1586,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1304,c_1583])).

tff(c_1590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1586])).

tff(c_1592,plain,(
    v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1582])).

tff(c_1547,plain,(
    ! [A_366,B_18] :
      ( '#skF_1'(u1_orders_2(A_366),B_18) != B_18
      | r7_orders_1(u1_orders_2(A_366),B_18)
      | ~ r2_hidden(B_18,u1_struct_0(A_366))
      | ~ v1_relat_1(u1_orders_2(A_366))
      | ~ v4_orders_2(A_366)
      | ~ v5_orders_2(A_366)
      | ~ v2_orders_2(A_366)
      | ~ l1_orders_2(A_366)
      | ~ v3_orders_2(A_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1528,c_18])).

tff(c_1472,plain,(
    ! [B_353,C_354,A_355] :
      ( r2_hidden(k4_tarski(B_353,C_354),u1_orders_2(A_355))
      | ~ r1_orders_2(A_355,B_353,C_354)
      | ~ m1_subset_1(C_354,u1_struct_0(A_355))
      | ~ m1_subset_1(B_353,u1_struct_0(A_355))
      | ~ l1_orders_2(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [C_21,B_18,A_12] :
      ( ~ r2_hidden(k4_tarski(C_21,B_18),A_12)
      | C_21 = B_18
      | ~ r2_hidden(C_21,k3_relat_1(A_12))
      | ~ r7_orders_1(A_12,B_18)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1662,plain,(
    ! [C_393,B_394,A_395] :
      ( C_393 = B_394
      | ~ r2_hidden(B_394,k3_relat_1(u1_orders_2(A_395)))
      | ~ r7_orders_1(u1_orders_2(A_395),C_393)
      | ~ v1_relat_1(u1_orders_2(A_395))
      | ~ r1_orders_2(A_395,B_394,C_393)
      | ~ m1_subset_1(C_393,u1_struct_0(A_395))
      | ~ m1_subset_1(B_394,u1_struct_0(A_395))
      | ~ l1_orders_2(A_395) ) ),
    inference(resolution,[status(thm)],[c_1472,c_12])).

tff(c_1681,plain,(
    ! [C_396,B_397,A_398] :
      ( C_396 = B_397
      | ~ r7_orders_1(u1_orders_2(A_398),C_396)
      | ~ r1_orders_2(A_398,B_397,C_396)
      | ~ m1_subset_1(C_396,u1_struct_0(A_398))
      | ~ m1_subset_1(B_397,u1_struct_0(A_398))
      | ~ l1_orders_2(A_398)
      | ~ r7_orders_1(u1_orders_2(A_398),B_397)
      | ~ v1_relat_1(u1_orders_2(A_398)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1662])).

tff(c_1688,plain,(
    ! [B_397] :
      ( B_397 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_397,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_397,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ r7_orders_1(u1_orders_2('#skF_2'),B_397)
      | ~ v1_relat_1(u1_orders_2('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1274,c_1681])).

tff(c_1694,plain,(
    ! [B_399] :
      ( B_399 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_399,'#skF_3')
      | ~ m1_subset_1(B_399,u1_struct_0('#skF_2'))
      | ~ r7_orders_1(u1_orders_2('#skF_2'),B_399) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1592,c_48,c_46,c_1688])).

tff(c_1698,plain,(
    ! [B_18] :
      ( B_18 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_18,'#skF_3')
      | ~ m1_subset_1(B_18,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_18) != B_18
      | ~ r2_hidden(B_18,u1_struct_0('#skF_2'))
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1547,c_1694])).

tff(c_1716,plain,(
    ! [B_400] :
      ( B_400 = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_400,'#skF_3')
      | ~ m1_subset_1(B_400,u1_struct_0('#skF_2'))
      | '#skF_1'(u1_orders_2('#skF_2'),B_400) != B_400
      | ~ r2_hidden(B_400,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1592,c_1698])).

tff(c_1733,plain,(
    ! [A_40] :
      ( A_40 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_40,'#skF_3')
      | '#skF_1'(u1_orders_2('#skF_2'),A_40) != A_40
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_40,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1716])).

tff(c_1735,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1733])).

tff(c_1738,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1735,c_32])).

tff(c_1741,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1738])).

tff(c_1744,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1741])).

tff(c_1748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1744])).

tff(c_1750,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1733])).

tff(c_1902,plain,(
    ! [C_421,A_422,A_423] :
      ( C_421 = A_422
      | ~ r7_orders_1(u1_orders_2(A_423),C_421)
      | ~ v1_relat_1(u1_orders_2(A_423))
      | ~ r1_orders_2(A_423,A_422,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_423))
      | ~ m1_subset_1(A_422,u1_struct_0(A_423))
      | ~ l1_orders_2(A_423)
      | v1_xboole_0(k3_relat_1(u1_orders_2(A_423)))
      | ~ m1_subset_1(A_422,k3_relat_1(u1_orders_2(A_423))) ) ),
    inference(resolution,[status(thm)],[c_44,c_1662])).

tff(c_1914,plain,(
    ! [A_422] :
      ( A_422 = '#skF_3'
      | ~ v1_relat_1(u1_orders_2('#skF_2'))
      | ~ r1_orders_2('#skF_2',A_422,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_422,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_422,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_1274,c_1902])).

tff(c_1921,plain,(
    ! [A_422] :
      ( A_422 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_422,'#skF_3')
      | ~ m1_subset_1(A_422,u1_struct_0('#skF_2'))
      | v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2')))
      | ~ m1_subset_1(A_422,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1592,c_1914])).

tff(c_1922,plain,(
    v1_xboole_0(k3_relat_1(u1_orders_2('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1921])).

tff(c_1925,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v2_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1922])).

tff(c_1927,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1925])).

tff(c_1929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1750,c_1927])).

tff(c_1994,plain,(
    ! [A_426] :
      ( A_426 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_426,'#skF_3')
      | ~ m1_subset_1(A_426,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_426,k3_relat_1(u1_orders_2('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_1921])).

tff(c_1997,plain,(
    ! [A_426] :
      ( A_426 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_426,'#skF_3')
      | ~ m1_subset_1(A_426,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_426,u1_struct_0('#skF_2'))
      | ~ v4_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v2_orders_2('#skF_2')
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1994])).

tff(c_2019,plain,(
    ! [A_427] :
      ( A_427 = '#skF_3'
      | ~ r1_orders_2('#skF_2',A_427,'#skF_3')
      | ~ m1_subset_1(A_427,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_77,c_50,c_52,c_1997])).

tff(c_2030,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1273,c_2019])).

tff(c_2040,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_2030])).

tff(c_2049,plain,(
    r2_orders_2('#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2040,c_1278])).

tff(c_8,plain,(
    ! [A_5,C_11] :
      ( ~ r2_orders_2(A_5,C_11,C_11)
      | ~ m1_subset_1(C_11,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2065,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_2049,c_8])).

tff(c_2072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1273,c_2065])).

%------------------------------------------------------------------------------
