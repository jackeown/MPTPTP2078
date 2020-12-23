%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1138+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:28 EST 2020

% Result     : Theorem 14.96s
% Output     : CNFRefutation 14.96s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 454 expanded)
%              Number of leaves         :   34 ( 176 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 (1697 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r8_relat_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v1_xboole_0 > v1_relat_1 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(r8_relat_2,type,(
    r8_relat_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r1_orders_2(A,B,C)
                        & r1_orders_2(A,C,D) )
                     => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v4_orders_2(A)
      <=> r8_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r8_relat_2(A,B)
        <=> ! [C,D,E] :
              ( ( r2_hidden(C,B)
                & r2_hidden(D,B)
                & r2_hidden(E,B)
                & r2_hidden(k4_tarski(C,D),A)
                & r2_hidden(k4_tarski(D,E),A) )
             => r2_hidden(k4_tarski(C,E),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).

tff(c_42,plain,(
    ~ r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_24,plain,(
    ! [B_33,C_35,A_29] :
      ( r2_hidden(k4_tarski(B_33,C_35),u1_orders_2(A_29))
      | ~ r1_orders_2(A_29,B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    ! [A_94] :
      ( m1_subset_1(u1_orders_2(A_94),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(A_94))))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_43,C_45,B_44] :
      ( m1_subset_1(A_43,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_111,plain,(
    ! [A_43,A_94] :
      ( m1_subset_1(A_43,k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(A_94)))
      | ~ r2_hidden(A_43,u1_orders_2(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(resolution,[status(thm)],[c_103,c_36])).

tff(c_34,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    ! [B_85,D_86,A_87,C_88] :
      ( r2_hidden(B_85,D_86)
      | ~ r2_hidden(k4_tarski(A_87,B_85),k2_zfmisc_1(C_88,D_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_178,plain,(
    ! [B_117,D_118,C_119,A_120] :
      ( r2_hidden(B_117,D_118)
      | v1_xboole_0(k2_zfmisc_1(C_119,D_118))
      | ~ m1_subset_1(k4_tarski(A_120,B_117),k2_zfmisc_1(C_119,D_118)) ) ),
    inference(resolution,[status(thm)],[c_34,c_87])).

tff(c_292,plain,(
    ! [B_165,A_166,A_167] :
      ( r2_hidden(B_165,u1_struct_0(A_166))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(A_166)))
      | ~ r2_hidden(k4_tarski(A_167,B_165),u1_orders_2(A_166))
      | ~ l1_orders_2(A_166) ) ),
    inference(resolution,[status(thm)],[c_111,c_178])).

tff(c_454,plain,(
    ! [C_204,A_205,B_206] :
      ( r2_hidden(C_204,u1_struct_0(A_205))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_205),u1_struct_0(A_205)))
      | ~ r1_orders_2(A_205,B_206,C_204)
      | ~ m1_subset_1(C_204,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205) ) ),
    inference(resolution,[status(thm)],[c_24,c_292])).

tff(c_456,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_454])).

tff(c_461,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_456])).

tff(c_465,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_461])).

tff(c_38,plain,(
    ! [C_48,B_47,A_46] :
      ( ~ v1_xboole_0(C_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_112,plain,(
    ! [A_94,A_46] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(A_94)))
      | ~ r2_hidden(A_46,u1_orders_2(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(resolution,[status(thm)],[c_103,c_38])).

tff(c_469,plain,(
    ! [A_46] :
      ( ~ r2_hidden(A_46,u1_orders_2('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_465,c_112])).

tff(c_474,plain,(
    ! [A_207] : ~ r2_hidden(A_207,u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_469])).

tff(c_478,plain,(
    ! [B_33,C_35] :
      ( ~ r1_orders_2('#skF_4',B_33,C_35)
      | ~ m1_subset_1(C_35,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_33,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_474])).

tff(c_626,plain,(
    ! [B_219,C_220] :
      ( ~ r1_orders_2('#skF_4',B_219,C_220)
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_219,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_478])).

tff(c_634,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_626])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_634])).

tff(c_648,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_76,plain,(
    ! [A_76,C_77,B_78,D_79] :
      ( r2_hidden(A_76,C_77)
      | ~ r2_hidden(k4_tarski(A_76,B_78),k2_zfmisc_1(C_77,D_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_184,plain,(
    ! [A_121,C_122,D_123,B_124] :
      ( r2_hidden(A_121,C_122)
      | v1_xboole_0(k2_zfmisc_1(C_122,D_123))
      | ~ m1_subset_1(k4_tarski(A_121,B_124),k2_zfmisc_1(C_122,D_123)) ) ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_275,plain,(
    ! [A_159,A_160,B_161] :
      ( r2_hidden(A_159,u1_struct_0(A_160))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_160),u1_struct_0(A_160)))
      | ~ r2_hidden(k4_tarski(A_159,B_161),u1_orders_2(A_160))
      | ~ l1_orders_2(A_160) ) ),
    inference(resolution,[status(thm)],[c_111,c_184])).

tff(c_662,plain,(
    ! [B_223,A_224,C_225] :
      ( r2_hidden(B_223,u1_struct_0(A_224))
      | v1_xboole_0(k2_zfmisc_1(u1_struct_0(A_224),u1_struct_0(A_224)))
      | ~ r1_orders_2(A_224,B_223,C_225)
      | ~ m1_subset_1(C_225,u1_struct_0(A_224))
      | ~ m1_subset_1(B_223,u1_struct_0(A_224))
      | ~ l1_orders_2(A_224) ) ),
    inference(resolution,[status(thm)],[c_24,c_275])).

tff(c_664,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_662])).

tff(c_669,plain,
    ( r2_hidden('#skF_5',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_664])).

tff(c_670,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_669])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    r1_orders_2('#skF_4','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_113,plain,(
    ! [A_94] :
      ( v1_relat_1(u1_orders_2(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_216,plain,(
    ! [B_137,C_138,A_139] :
      ( r2_hidden(k4_tarski(B_137,C_138),u1_orders_2(A_139))
      | ~ r1_orders_2(A_139,B_137,C_138)
      | ~ m1_subset_1(C_138,u1_struct_0(A_139))
      | ~ m1_subset_1(B_137,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [B_50,A_49] :
      ( ~ v1_xboole_0(B_50)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_247,plain,(
    ! [A_151,B_152,C_153] :
      ( ~ v1_xboole_0(u1_orders_2(A_151))
      | ~ r1_orders_2(A_151,B_152,C_153)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_216,c_40])).

tff(c_249,plain,
    ( ~ v1_xboole_0(u1_orders_2('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_247])).

tff(c_254,plain,(
    ~ v1_xboole_0(u1_orders_2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_249])).

tff(c_6,plain,(
    ! [A_4] :
      ( r8_relat_2(u1_orders_2(A_4),u1_struct_0(A_4))
      | ~ v4_orders_2(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_647,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_461])).

tff(c_652,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_647,c_40])).

tff(c_258,plain,(
    ! [C_154,A_156,E_155,D_158,B_157] :
      ( r2_hidden(k4_tarski(C_154,E_155),A_156)
      | ~ r2_hidden(k4_tarski(D_158,E_155),A_156)
      | ~ r2_hidden(k4_tarski(C_154,D_158),A_156)
      | ~ r2_hidden(E_155,B_157)
      | ~ r2_hidden(D_158,B_157)
      | ~ r2_hidden(C_154,B_157)
      | ~ r8_relat_2(A_156,B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_437,plain,(
    ! [C_200,B_203,E_199,D_202,B_201] :
      ( r2_hidden(k4_tarski(C_200,E_199),B_203)
      | ~ r2_hidden(k4_tarski(C_200,D_202),B_203)
      | ~ r2_hidden(E_199,B_201)
      | ~ r2_hidden(D_202,B_201)
      | ~ r2_hidden(C_200,B_201)
      | ~ r8_relat_2(B_203,B_201)
      | ~ v1_relat_1(B_203)
      | v1_xboole_0(B_203)
      | ~ m1_subset_1(k4_tarski(D_202,E_199),B_203) ) ),
    inference(resolution,[status(thm)],[c_34,c_258])).

tff(c_679,plain,(
    ! [D_227,B_226,E_228,C_229,B_230] :
      ( r2_hidden(k4_tarski(C_229,E_228),B_230)
      | ~ r2_hidden(E_228,B_226)
      | ~ r2_hidden(D_227,B_226)
      | ~ r2_hidden(C_229,B_226)
      | ~ r8_relat_2(B_230,B_226)
      | ~ v1_relat_1(B_230)
      | ~ m1_subset_1(k4_tarski(D_227,E_228),B_230)
      | v1_xboole_0(B_230)
      | ~ m1_subset_1(k4_tarski(C_229,D_227),B_230) ) ),
    inference(resolution,[status(thm)],[c_34,c_437])).

tff(c_956,plain,(
    ! [C_249,B_250,D_251] :
      ( r2_hidden(k4_tarski(C_249,'#skF_6'),B_250)
      | ~ r2_hidden(D_251,u1_struct_0('#skF_4'))
      | ~ r2_hidden(C_249,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_250,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_250)
      | ~ m1_subset_1(k4_tarski(D_251,'#skF_6'),B_250)
      | v1_xboole_0(B_250)
      | ~ m1_subset_1(k4_tarski(C_249,D_251),B_250) ) ),
    inference(resolution,[status(thm)],[c_647,c_679])).

tff(c_989,plain,(
    ! [C_249,B_250,A_41] :
      ( r2_hidden(k4_tarski(C_249,'#skF_6'),B_250)
      | ~ r2_hidden(C_249,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_250,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_250)
      | ~ m1_subset_1(k4_tarski(A_41,'#skF_6'),B_250)
      | v1_xboole_0(B_250)
      | ~ m1_subset_1(k4_tarski(C_249,A_41),B_250)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_41,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_956])).

tff(c_1063,plain,(
    ! [C_256,B_257,A_258] :
      ( r2_hidden(k4_tarski(C_256,'#skF_6'),B_257)
      | ~ r2_hidden(C_256,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(B_257,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(B_257)
      | ~ m1_subset_1(k4_tarski(A_258,'#skF_6'),B_257)
      | v1_xboole_0(B_257)
      | ~ m1_subset_1(k4_tarski(C_256,A_258),B_257)
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_652,c_989])).

tff(c_1078,plain,(
    ! [C_256,A_258] :
      ( r2_hidden(k4_tarski(C_256,'#skF_6'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(C_256,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(A_258,'#skF_6'),u1_orders_2('#skF_4'))
      | v1_xboole_0(u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(C_256,A_258),u1_orders_2('#skF_4'))
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4'))
      | ~ v4_orders_2('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_1063])).

tff(c_1085,plain,(
    ! [C_256,A_258] :
      ( r2_hidden(k4_tarski(C_256,'#skF_6'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(C_256,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(A_258,'#skF_6'),u1_orders_2('#skF_4'))
      | v1_xboole_0(u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(C_256,A_258),u1_orders_2('#skF_4'))
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1078])).

tff(c_1086,plain,(
    ! [C_256,A_258] :
      ( r2_hidden(k4_tarski(C_256,'#skF_6'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(C_256,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(A_258,'#skF_6'),u1_orders_2('#skF_4'))
      | ~ m1_subset_1(k4_tarski(C_256,A_258),u1_orders_2('#skF_4'))
      | ~ m1_subset_1(A_258,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_1085])).

tff(c_1098,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1101,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_1098])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1101])).

tff(c_1107,plain,(
    v1_relat_1(u1_orders_2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_458,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_454])).

tff(c_464,plain,
    ( r2_hidden('#skF_7',u1_struct_0('#skF_4'))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_458])).

tff(c_653,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_648,c_653])).

tff(c_655,plain,(
    r2_hidden('#skF_7',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_1579,plain,(
    ! [C_320,C_322,B_321,B_324,A_323] :
      ( r2_hidden(k4_tarski(C_322,C_320),u1_orders_2(A_323))
      | ~ r2_hidden(k4_tarski(C_322,B_321),u1_orders_2(A_323))
      | ~ r2_hidden(C_320,B_324)
      | ~ r2_hidden(B_321,B_324)
      | ~ r2_hidden(C_322,B_324)
      | ~ r8_relat_2(u1_orders_2(A_323),B_324)
      | ~ v1_relat_1(u1_orders_2(A_323))
      | ~ r1_orders_2(A_323,B_321,C_320)
      | ~ m1_subset_1(C_320,u1_struct_0(A_323))
      | ~ m1_subset_1(B_321,u1_struct_0(A_323))
      | ~ l1_orders_2(A_323) ) ),
    inference(resolution,[status(thm)],[c_24,c_258])).

tff(c_3771,plain,(
    ! [B_484,C_482,B_483,A_486,C_485] :
      ( r2_hidden(k4_tarski(B_484,C_485),u1_orders_2(A_486))
      | ~ r2_hidden(C_485,B_483)
      | ~ r2_hidden(C_482,B_483)
      | ~ r2_hidden(B_484,B_483)
      | ~ r8_relat_2(u1_orders_2(A_486),B_483)
      | ~ v1_relat_1(u1_orders_2(A_486))
      | ~ r1_orders_2(A_486,C_482,C_485)
      | ~ m1_subset_1(C_485,u1_struct_0(A_486))
      | ~ r1_orders_2(A_486,B_484,C_482)
      | ~ m1_subset_1(C_482,u1_struct_0(A_486))
      | ~ m1_subset_1(B_484,u1_struct_0(A_486))
      | ~ l1_orders_2(A_486) ) ),
    inference(resolution,[status(thm)],[c_24,c_1579])).

tff(c_15920,plain,(
    ! [B_1107,A_1108,C_1109] :
      ( r2_hidden(k4_tarski(B_1107,'#skF_7'),u1_orders_2(A_1108))
      | ~ r2_hidden(C_1109,u1_struct_0('#skF_4'))
      | ~ r2_hidden(B_1107,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_1108),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_1108))
      | ~ r1_orders_2(A_1108,C_1109,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_1108))
      | ~ r1_orders_2(A_1108,B_1107,C_1109)
      | ~ m1_subset_1(C_1109,u1_struct_0(A_1108))
      | ~ m1_subset_1(B_1107,u1_struct_0(A_1108))
      | ~ l1_orders_2(A_1108) ) ),
    inference(resolution,[status(thm)],[c_655,c_3771])).

tff(c_16513,plain,(
    ! [B_1126,A_1127] :
      ( r2_hidden(k4_tarski(B_1126,'#skF_7'),u1_orders_2(A_1127))
      | ~ r2_hidden(B_1126,u1_struct_0('#skF_4'))
      | ~ r8_relat_2(u1_orders_2(A_1127),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2(A_1127))
      | ~ r1_orders_2(A_1127,'#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0(A_1127))
      | ~ r1_orders_2(A_1127,B_1126,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_1127))
      | ~ m1_subset_1(B_1126,u1_struct_0(A_1127))
      | ~ l1_orders_2(A_1127) ) ),
    inference(resolution,[status(thm)],[c_647,c_15920])).

tff(c_16527,plain,(
    ! [B_1126] :
      ( r2_hidden(k4_tarski(B_1126,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_1126,u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_orders_2('#skF_4'))
      | ~ r1_orders_2('#skF_4','#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1126,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_1126,u1_struct_0('#skF_4'))
      | ~ v4_orders_2('#skF_4')
      | ~ l1_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_16513])).

tff(c_16537,plain,(
    ! [B_1128] :
      ( r2_hidden(k4_tarski(B_1128,'#skF_7'),u1_orders_2('#skF_4'))
      | ~ r2_hidden(B_1128,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1128,'#skF_6')
      | ~ m1_subset_1(B_1128,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_50,c_48,c_44,c_1107,c_16527])).

tff(c_22,plain,(
    ! [A_29,B_33,C_35] :
      ( r1_orders_2(A_29,B_33,C_35)
      | ~ r2_hidden(k4_tarski(B_33,C_35),u1_orders_2(A_29))
      | ~ m1_subset_1(C_35,u1_struct_0(A_29))
      | ~ m1_subset_1(B_33,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16610,plain,(
    ! [B_1128] :
      ( r1_orders_2('#skF_4',B_1128,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden(B_1128,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1128,'#skF_6')
      | ~ m1_subset_1(B_1128,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16537,c_22])).

tff(c_16690,plain,(
    ! [B_1129] :
      ( r1_orders_2('#skF_4',B_1129,'#skF_7')
      | ~ r2_hidden(B_1129,u1_struct_0('#skF_4'))
      | ~ r1_orders_2('#skF_4',B_1129,'#skF_6')
      | ~ m1_subset_1(B_1129,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_16610])).

tff(c_16813,plain,
    ( r1_orders_2('#skF_4','#skF_5','#skF_7')
    | ~ r1_orders_2('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_670,c_16690])).

tff(c_16924,plain,(
    r1_orders_2('#skF_4','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_16813])).

tff(c_16926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_16924])).

%------------------------------------------------------------------------------
