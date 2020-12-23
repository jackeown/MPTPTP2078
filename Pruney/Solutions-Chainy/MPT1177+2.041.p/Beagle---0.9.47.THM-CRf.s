%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:01 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 299 expanded)
%              Number of leaves         :   39 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  338 (1292 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ( r2_xboole_0(C,D)
                    <=> m1_orders_2(C,A,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

tff(f_70,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ~ ( B != k1_xboole_0
                  & m1_orders_2(B,A,C)
                  & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => m2_orders_2(k1_tarski(k1_funct_1(B,u1_struct_0(A))),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_orders_2)).

tff(f_149,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_177,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ( C != D
                   => ( m1_orders_2(C,A,D)
                    <=> ~ m1_orders_2(D,A,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

tff(c_4,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_48,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_46,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_44,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_42,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_40,plain,(
    m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    m2_orders_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_168,plain,(
    ! [C_107,A_108,B_109] :
      ( m1_subset_1(C_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m2_orders_2(C_107,A_108,B_109)
      | ~ m1_orders_1(B_109,k1_orders_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_168])).

tff(c_176,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_172])).

tff(c_177,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_176])).

tff(c_73,plain,(
    ! [A_72,B_73] :
      ( r2_xboole_0(A_72,B_73)
      | B_73 = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,
    ( ~ m1_orders_2('#skF_3','#skF_1','#skF_4')
    | ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_63,plain,(
    ~ r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_84,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_63])).

tff(c_90,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_58,plain,
    ( r2_xboole_0('#skF_3','#skF_4')
    | m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_64,plain,(
    m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_58])).

tff(c_109,plain,(
    ! [C_83,B_84,A_85] :
      ( r1_tarski(C_83,B_84)
      | ~ m1_orders_2(C_83,A_85,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85)
      | ~ v5_orders_2(A_85)
      | ~ v4_orders_2(A_85)
      | ~ v3_orders_2(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_111,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_109])).

tff(c_114,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_111])).

tff(c_115,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_90,c_114])).

tff(c_121,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m2_orders_2(C_90,A_91,B_92)
      | ~ m1_orders_1(B_92,k1_orders_1(u1_struct_0(A_91)))
      | ~ l1_orders_2(A_91)
      | ~ v5_orders_2(A_91)
      | ~ v4_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_131,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_125])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_115,c_131])).

tff(c_134,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_136,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64])).

tff(c_202,plain,(
    ! [C_124,A_125,B_126] :
      ( ~ m1_orders_2(C_124,A_125,B_126)
      | ~ m1_orders_2(B_126,A_125,C_124)
      | k1_xboole_0 = B_126
      | ~ m1_subset_1(C_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_orders_2(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v4_orders_2(A_125)
      | ~ v3_orders_2(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_204,plain,
    ( ~ m1_orders_2('#skF_4','#skF_1','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_136,c_202])).

tff(c_207,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_177,c_136,c_204])).

tff(c_208,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_207])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_8])).

tff(c_28,plain,(
    ! [B_30,A_28] :
      ( m2_orders_2(k1_tarski(k1_funct_1(B_30,u1_struct_0(A_28))),A_28,B_30)
      | ~ m1_orders_1(B_30,k1_orders_1(u1_struct_0(A_28)))
      | ~ l1_orders_2(A_28)
      | ~ v5_orders_2(A_28)
      | ~ v4_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_30,plain,(
    ! [B_35,A_31,C_37] :
      ( r2_hidden(k1_funct_1(B_35,u1_struct_0(A_31)),C_37)
      | ~ m2_orders_2(C_37,A_31,B_35)
      | ~ m1_orders_1(B_35,k1_orders_1(u1_struct_0(A_31)))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_187,plain,(
    ! [B_114,A_115,C_116] :
      ( r2_hidden(k1_funct_1(B_114,u1_struct_0(A_115)),C_116)
      | ~ m2_orders_2(C_116,A_115,B_114)
      | ~ m1_orders_1(B_114,k1_orders_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(B_6))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [C_93,B_94,A_95] :
      ( ~ v1_xboole_0(C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_148,plain,(
    ! [B_6,A_95,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_95,k1_tarski(A_5))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_145])).

tff(c_198,plain,(
    ! [B_120,A_121,A_122,B_123] :
      ( ~ v1_xboole_0(B_120)
      | ~ r2_hidden(A_121,B_120)
      | ~ m2_orders_2(k1_tarski(A_121),A_122,B_123)
      | ~ m1_orders_1(B_123,k1_orders_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_187,c_148])).

tff(c_422,plain,(
    ! [A_155,A_154,C_156,B_157,B_158] :
      ( ~ v1_xboole_0(C_156)
      | ~ m2_orders_2(k1_tarski(k1_funct_1(B_157,u1_struct_0(A_154))),A_155,B_158)
      | ~ m1_orders_1(B_158,k1_orders_1(u1_struct_0(A_155)))
      | ~ l1_orders_2(A_155)
      | ~ v5_orders_2(A_155)
      | ~ v4_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155)
      | ~ m2_orders_2(C_156,A_154,B_157)
      | ~ m1_orders_1(B_157,k1_orders_1(u1_struct_0(A_154)))
      | ~ l1_orders_2(A_154)
      | ~ v5_orders_2(A_154)
      | ~ v4_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_30,c_198])).

tff(c_443,plain,(
    ! [C_162,A_163,B_164] :
      ( ~ v1_xboole_0(C_162)
      | ~ m2_orders_2(C_162,A_163,B_164)
      | ~ m1_orders_1(B_164,k1_orders_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_28,c_422])).

tff(c_447,plain,
    ( ~ v1_xboole_0('#skF_4')
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_443])).

tff(c_451,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_210,c_447])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_451])).

tff(c_455,plain,(
    r2_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_459,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_455,c_6])).

tff(c_475,plain,(
    ! [B_169,A_170] :
      ( B_169 = A_170
      | ~ r1_tarski(B_169,A_170)
      | ~ r1_tarski(A_170,B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_480,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_459,c_475])).

tff(c_485,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_480])).

tff(c_38,plain,(
    m2_orders_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_510,plain,(
    ! [C_187,A_188,B_189] :
      ( m1_subset_1(C_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ m2_orders_2(C_187,A_188,B_189)
      | ~ m1_orders_1(B_189,k1_orders_1(u1_struct_0(A_188)))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_516,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_510])).

tff(c_524,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_516])).

tff(c_525,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_524])).

tff(c_14,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_454,plain,(
    ~ m1_orders_2('#skF_3','#skF_1','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_555,plain,(
    ! [C_209,A_210,D_211,B_212] :
      ( m1_orders_2(C_209,A_210,D_211)
      | m1_orders_2(D_211,A_210,C_209)
      | D_211 = C_209
      | ~ m2_orders_2(D_211,A_210,B_212)
      | ~ m2_orders_2(C_209,A_210,B_212)
      | ~ m1_orders_1(B_212,k1_orders_1(u1_struct_0(A_210)))
      | ~ l1_orders_2(A_210)
      | ~ v5_orders_2(A_210)
      | ~ v4_orders_2(A_210)
      | ~ v3_orders_2(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_559,plain,(
    ! [C_209] :
      ( m1_orders_2(C_209,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_209)
      | C_209 = '#skF_4'
      | ~ m2_orders_2(C_209,'#skF_1','#skF_2')
      | ~ m1_orders_1('#skF_2',k1_orders_1(u1_struct_0('#skF_1')))
      | ~ l1_orders_2('#skF_1')
      | ~ v5_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1')
      | ~ v3_orders_2('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_555])).

tff(c_565,plain,(
    ! [C_209] :
      ( m1_orders_2(C_209,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_209)
      | C_209 = '#skF_4'
      | ~ m2_orders_2(C_209,'#skF_1','#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_559])).

tff(c_571,plain,(
    ! [C_213] :
      ( m1_orders_2(C_213,'#skF_1','#skF_4')
      | m1_orders_2('#skF_4','#skF_1',C_213)
      | C_213 = '#skF_4'
      | ~ m2_orders_2(C_213,'#skF_1','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_565])).

tff(c_581,plain,
    ( m1_orders_2('#skF_3','#skF_1','#skF_4')
    | m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_571])).

tff(c_590,plain,
    ( m1_orders_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_581])).

tff(c_611,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_615,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_485])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_615])).

tff(c_625,plain,(
    m1_orders_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_24,plain,(
    ! [C_20,B_18,A_14] :
      ( r1_tarski(C_20,B_18)
      | ~ m1_orders_2(C_20,A_14,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_orders_2(A_14)
      | ~ v5_orders_2(A_14)
      | ~ v4_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_632,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_625,c_24])).

tff(c_643,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_525,c_632])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_485,c_643])).

tff(c_646,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_480])).

tff(c_650,plain,(
    r2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_455])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.75  
% 3.71/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.75  %$ m2_orders_2 > m1_orders_2 > v6_orders_2 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.71/1.75  
% 3.71/1.75  %Foreground sorts:
% 3.71/1.75  
% 3.71/1.75  
% 3.71/1.75  %Background operators:
% 3.71/1.75  
% 3.71/1.75  
% 3.71/1.75  %Foreground operators:
% 3.71/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.71/1.75  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.71/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.71/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.75  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.71/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.75  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.71/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.71/1.75  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.71/1.75  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.71/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.75  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.71/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.71/1.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.71/1.75  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.71/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.75  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.71/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.75  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.71/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.71/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.75  
% 3.71/1.77  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.71/1.77  tff(f_202, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (r2_xboole_0(C, D) <=> m1_orders_2(C, A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 3.71/1.77  tff(f_70, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.71/1.77  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 3.71/1.77  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.71/1.77  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.71/1.77  tff(f_130, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => m2_orders_2(k1_tarski(k1_funct_1(B, u1_struct_0(A))), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_orders_2)).
% 3.71/1.77  tff(f_149, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 3.71/1.77  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.71/1.77  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.71/1.77  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.71/1.77  tff(f_177, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => (~(C = D) => (m1_orders_2(C, A, D) <=> ~m1_orders_2(D, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 3.71/1.77  tff(c_4, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.77  tff(c_50, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_48, plain, (v3_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_46, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_44, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_42, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_40, plain, (m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_36, plain, (m2_orders_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_168, plain, (![C_107, A_108, B_109]: (m1_subset_1(C_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~m2_orders_2(C_107, A_108, B_109) | ~m1_orders_1(B_109, k1_orders_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.77  tff(c_172, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_168])).
% 3.71/1.77  tff(c_176, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_172])).
% 3.71/1.77  tff(c_177, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_176])).
% 3.71/1.77  tff(c_73, plain, (![A_72, B_73]: (r2_xboole_0(A_72, B_73) | B_73=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.77  tff(c_52, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4') | ~r2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_63, plain, (~r2_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.71/1.77  tff(c_84, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_73, c_63])).
% 3.71/1.77  tff(c_90, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 3.71/1.77  tff(c_58, plain, (r2_xboole_0('#skF_3', '#skF_4') | m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_64, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_63, c_58])).
% 3.71/1.77  tff(c_109, plain, (![C_83, B_84, A_85]: (r1_tarski(C_83, B_84) | ~m1_orders_2(C_83, A_85, B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_orders_2(A_85) | ~v5_orders_2(A_85) | ~v4_orders_2(A_85) | ~v3_orders_2(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.71/1.77  tff(c_111, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_109])).
% 3.71/1.77  tff(c_114, plain, (r1_tarski('#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_111])).
% 3.71/1.77  tff(c_115, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_90, c_114])).
% 3.71/1.77  tff(c_121, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m2_orders_2(C_90, A_91, B_92) | ~m1_orders_1(B_92, k1_orders_1(u1_struct_0(A_91))) | ~l1_orders_2(A_91) | ~v5_orders_2(A_91) | ~v4_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.77  tff(c_125, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_121])).
% 3.71/1.77  tff(c_131, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_125])).
% 3.71/1.77  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_115, c_131])).
% 3.71/1.77  tff(c_134, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_84])).
% 3.71/1.77  tff(c_136, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64])).
% 3.71/1.77  tff(c_202, plain, (![C_124, A_125, B_126]: (~m1_orders_2(C_124, A_125, B_126) | ~m1_orders_2(B_126, A_125, C_124) | k1_xboole_0=B_126 | ~m1_subset_1(C_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_orders_2(A_125) | ~v5_orders_2(A_125) | ~v4_orders_2(A_125) | ~v3_orders_2(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.71/1.77  tff(c_204, plain, (~m1_orders_2('#skF_4', '#skF_1', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_136, c_202])).
% 3.71/1.77  tff(c_207, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_177, c_136, c_204])).
% 3.71/1.77  tff(c_208, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_50, c_207])).
% 3.71/1.77  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.71/1.77  tff(c_210, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_8])).
% 3.71/1.77  tff(c_28, plain, (![B_30, A_28]: (m2_orders_2(k1_tarski(k1_funct_1(B_30, u1_struct_0(A_28))), A_28, B_30) | ~m1_orders_1(B_30, k1_orders_1(u1_struct_0(A_28))) | ~l1_orders_2(A_28) | ~v5_orders_2(A_28) | ~v4_orders_2(A_28) | ~v3_orders_2(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.71/1.77  tff(c_30, plain, (![B_35, A_31, C_37]: (r2_hidden(k1_funct_1(B_35, u1_struct_0(A_31)), C_37) | ~m2_orders_2(C_37, A_31, B_35) | ~m1_orders_1(B_35, k1_orders_1(u1_struct_0(A_31))) | ~l1_orders_2(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.71/1.77  tff(c_187, plain, (![B_114, A_115, C_116]: (r2_hidden(k1_funct_1(B_114, u1_struct_0(A_115)), C_116) | ~m2_orders_2(C_116, A_115, B_114) | ~m1_orders_1(B_114, k1_orders_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.71/1.77  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(B_6)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.71/1.77  tff(c_145, plain, (![C_93, B_94, A_95]: (~v1_xboole_0(C_93) | ~m1_subset_1(B_94, k1_zfmisc_1(C_93)) | ~r2_hidden(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.71/1.77  tff(c_148, plain, (![B_6, A_95, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_95, k1_tarski(A_5)) | ~r2_hidden(A_5, B_6))), inference(resolution, [status(thm)], [c_16, c_145])).
% 3.71/1.77  tff(c_198, plain, (![B_120, A_121, A_122, B_123]: (~v1_xboole_0(B_120) | ~r2_hidden(A_121, B_120) | ~m2_orders_2(k1_tarski(A_121), A_122, B_123) | ~m1_orders_1(B_123, k1_orders_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_187, c_148])).
% 3.71/1.77  tff(c_422, plain, (![A_155, A_154, C_156, B_157, B_158]: (~v1_xboole_0(C_156) | ~m2_orders_2(k1_tarski(k1_funct_1(B_157, u1_struct_0(A_154))), A_155, B_158) | ~m1_orders_1(B_158, k1_orders_1(u1_struct_0(A_155))) | ~l1_orders_2(A_155) | ~v5_orders_2(A_155) | ~v4_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155) | ~m2_orders_2(C_156, A_154, B_157) | ~m1_orders_1(B_157, k1_orders_1(u1_struct_0(A_154))) | ~l1_orders_2(A_154) | ~v5_orders_2(A_154) | ~v4_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_30, c_198])).
% 3.71/1.77  tff(c_443, plain, (![C_162, A_163, B_164]: (~v1_xboole_0(C_162) | ~m2_orders_2(C_162, A_163, B_164) | ~m1_orders_1(B_164, k1_orders_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_28, c_422])).
% 3.71/1.77  tff(c_447, plain, (~v1_xboole_0('#skF_4') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_443])).
% 3.71/1.77  tff(c_451, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_210, c_447])).
% 3.71/1.77  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_451])).
% 3.71/1.77  tff(c_455, plain, (r2_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.71/1.77  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.77  tff(c_459, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_455, c_6])).
% 3.71/1.77  tff(c_475, plain, (![B_169, A_170]: (B_169=A_170 | ~r1_tarski(B_169, A_170) | ~r1_tarski(A_170, B_169))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.77  tff(c_480, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_459, c_475])).
% 3.71/1.77  tff(c_485, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_480])).
% 3.71/1.77  tff(c_38, plain, (m2_orders_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 3.71/1.77  tff(c_510, plain, (![C_187, A_188, B_189]: (m1_subset_1(C_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~m2_orders_2(C_187, A_188, B_189) | ~m1_orders_1(B_189, k1_orders_1(u1_struct_0(A_188))) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.77  tff(c_516, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_510])).
% 3.71/1.77  tff(c_524, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_516])).
% 3.71/1.77  tff(c_525, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_50, c_524])).
% 3.71/1.77  tff(c_14, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.77  tff(c_454, plain, (~m1_orders_2('#skF_3', '#skF_1', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.71/1.77  tff(c_555, plain, (![C_209, A_210, D_211, B_212]: (m1_orders_2(C_209, A_210, D_211) | m1_orders_2(D_211, A_210, C_209) | D_211=C_209 | ~m2_orders_2(D_211, A_210, B_212) | ~m2_orders_2(C_209, A_210, B_212) | ~m1_orders_1(B_212, k1_orders_1(u1_struct_0(A_210))) | ~l1_orders_2(A_210) | ~v5_orders_2(A_210) | ~v4_orders_2(A_210) | ~v3_orders_2(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.71/1.77  tff(c_559, plain, (![C_209]: (m1_orders_2(C_209, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_209) | C_209='#skF_4' | ~m2_orders_2(C_209, '#skF_1', '#skF_2') | ~m1_orders_1('#skF_2', k1_orders_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_555])).
% 3.71/1.77  tff(c_565, plain, (![C_209]: (m1_orders_2(C_209, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_209) | C_209='#skF_4' | ~m2_orders_2(C_209, '#skF_1', '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_559])).
% 3.71/1.77  tff(c_571, plain, (![C_213]: (m1_orders_2(C_213, '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', C_213) | C_213='#skF_4' | ~m2_orders_2(C_213, '#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_565])).
% 3.71/1.77  tff(c_581, plain, (m1_orders_2('#skF_3', '#skF_1', '#skF_4') | m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_38, c_571])).
% 3.71/1.77  tff(c_590, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_454, c_581])).
% 3.71/1.77  tff(c_611, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_590])).
% 3.71/1.77  tff(c_615, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_485])).
% 3.71/1.77  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_615])).
% 3.71/1.77  tff(c_625, plain, (m1_orders_2('#skF_4', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_590])).
% 3.71/1.77  tff(c_24, plain, (![C_20, B_18, A_14]: (r1_tarski(C_20, B_18) | ~m1_orders_2(C_20, A_14, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_orders_2(A_14) | ~v5_orders_2(A_14) | ~v4_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.71/1.77  tff(c_632, plain, (r1_tarski('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1') | ~v4_orders_2('#skF_1') | ~v3_orders_2('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_625, c_24])).
% 3.71/1.77  tff(c_643, plain, (r1_tarski('#skF_4', '#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_525, c_632])).
% 3.71/1.77  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_485, c_643])).
% 3.71/1.77  tff(c_646, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_480])).
% 3.71/1.77  tff(c_650, plain, (r2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_646, c_455])).
% 3.71/1.77  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4, c_650])).
% 3.71/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.77  
% 3.71/1.77  Inference rules
% 3.71/1.77  ----------------------
% 3.71/1.77  #Ref     : 0
% 3.71/1.77  #Sup     : 99
% 3.71/1.77  #Fact    : 2
% 3.71/1.77  #Define  : 0
% 3.71/1.77  #Split   : 11
% 3.71/1.77  #Chain   : 0
% 3.71/1.77  #Close   : 0
% 3.71/1.77  
% 3.71/1.77  Ordering : KBO
% 3.71/1.77  
% 3.71/1.77  Simplification rules
% 3.71/1.77  ----------------------
% 3.71/1.77  #Subsume      : 15
% 3.71/1.77  #Demod        : 235
% 3.71/1.77  #Tautology    : 38
% 3.71/1.77  #SimpNegUnit  : 43
% 3.71/1.77  #BackRed      : 17
% 3.71/1.78  
% 3.71/1.78  #Partial instantiations: 0
% 3.71/1.78  #Strategies tried      : 1
% 3.71/1.78  
% 3.71/1.78  Timing (in seconds)
% 3.71/1.78  ----------------------
% 3.71/1.78  Preprocessing        : 0.41
% 3.71/1.78  Parsing              : 0.24
% 3.71/1.78  CNF conversion       : 0.03
% 3.71/1.78  Main loop            : 0.51
% 3.71/1.78  Inferencing          : 0.21
% 3.71/1.78  Reduction            : 0.15
% 3.71/1.78  Demodulation         : 0.11
% 3.71/1.78  BG Simplification    : 0.03
% 3.71/1.78  Subsumption          : 0.09
% 3.71/1.78  Abstraction          : 0.02
% 3.71/1.78  MUC search           : 0.00
% 3.71/1.78  Cooper               : 0.00
% 3.71/1.78  Total                : 0.98
% 3.71/1.78  Index Insertion      : 0.00
% 3.71/1.78  Index Deletion       : 0.00
% 3.71/1.78  Index Matching       : 0.00
% 3.71/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
