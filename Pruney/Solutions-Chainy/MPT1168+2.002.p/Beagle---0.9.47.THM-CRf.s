%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:51 EST 2020

% Result     : Theorem 6.91s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 369 expanded)
%              Number of leaves         :   29 ( 152 expanded)
%              Depth                    :   19
%              Number of atoms          :  554 (1955 expanded)
%              Number of equality atoms :    8 (  99 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( r2_hidden(B,C)
                        & m1_orders_2(C,A,D) )
                     => k3_orders_2(A,C,B) = k3_orders_2(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                     => ( ( r2_orders_2(A,B,C)
                          & r2_hidden(B,D)
                          & r2_hidden(C,E)
                          & m1_orders_2(E,A,D) )
                       => r2_hidden(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

tff(f_106,axiom,(
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

tff(c_28,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k3_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_32,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_46,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_44,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_42,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_40,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [C_85,B_86,A_87] :
      ( r2_hidden(C_85,B_86)
      | ~ r2_hidden(C_85,A_87)
      | ~ r1_tarski(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_1,B_2,B_86] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_86)
      | ~ r1_tarski(A_1,B_86)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_121,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1(k3_orders_2(A_106,B_107,C_108),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_249,plain,(
    ! [A_135,A_136,B_137,C_138] :
      ( m1_subset_1(A_135,u1_struct_0(A_136))
      | ~ r2_hidden(A_135,k3_orders_2(A_136,B_137,C_138))
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_121,c_14])).

tff(c_474,plain,(
    ! [A_195,B_192,A_194,C_191,B_193] :
      ( m1_subset_1('#skF_1'(A_194,B_192),u1_struct_0(A_195))
      | ~ m1_subset_1(C_191,u1_struct_0(A_195))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_orders_2(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v4_orders_2(A_195)
      | ~ v3_orders_2(A_195)
      | v2_struct_0(A_195)
      | ~ r1_tarski(A_194,k3_orders_2(A_195,B_193,C_191))
      | r1_tarski(A_194,B_192) ) ),
    inference(resolution,[status(thm)],[c_71,c_249])).

tff(c_478,plain,(
    ! [A_194,B_192,C_191] :
      ( m1_subset_1('#skF_1'(A_194,B_192),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_194,k3_orders_2('#skF_2','#skF_5',C_191))
      | r1_tarski(A_194,B_192) ) ),
    inference(resolution,[status(thm)],[c_34,c_474])).

tff(c_484,plain,(
    ! [A_194,B_192,C_191] :
      ( m1_subset_1('#skF_1'(A_194,B_192),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_194,k3_orders_2('#skF_2','#skF_5',C_191))
      | r1_tarski(A_194,B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_478])).

tff(c_490,plain,(
    ! [A_196,B_197,C_198] :
      ( m1_subset_1('#skF_1'(A_196,B_197),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_196,k3_orders_2('#skF_2','#skF_5',C_198))
      | r1_tarski(A_196,B_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_484])).

tff(c_494,plain,(
    ! [C_198,B_197] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198),B_197),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_198),B_197) ) ),
    inference(resolution,[status(thm)],[c_12,c_490])).

tff(c_183,plain,(
    ! [B_119,D_120,A_121,C_122] :
      ( r2_hidden(B_119,D_120)
      | ~ r2_hidden(B_119,k3_orders_2(A_121,D_120,C_122))
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_subset_1(C_122,u1_struct_0(A_121))
      | ~ m1_subset_1(B_119,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_501,plain,(
    ! [A_204,D_205,C_206,B_207] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_204,D_205,C_206),B_207),D_205)
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(C_206,u1_struct_0(A_204))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_204,D_205,C_206),B_207),u1_struct_0(A_204))
      | ~ l1_orders_2(A_204)
      | ~ v5_orders_2(A_204)
      | ~ v4_orders_2(A_204)
      | ~ v3_orders_2(A_204)
      | v2_struct_0(A_204)
      | r1_tarski(k3_orders_2(A_204,D_205,C_206),B_207) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_503,plain,(
    ! [C_198,B_197] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198),B_197),'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_198),B_197) ) ),
    inference(resolution,[status(thm)],[c_494,c_501])).

tff(c_514,plain,(
    ! [C_198,B_197] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_198),B_197),'#skF_5')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_198),B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_503])).

tff(c_525,plain,(
    ! [C_208,B_209] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_208),B_209),'#skF_5')
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),B_209) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_514])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_532,plain,(
    ! [C_208,B_209,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_208),B_209),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_525,c_2])).

tff(c_81,plain,(
    ! [A_91,C_92,B_93] :
      ( m1_subset_1(A_91,C_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_92))
      | ~ r2_hidden(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_81])).

tff(c_318,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( r2_orders_2(A_148,B_149,C_150)
      | ~ r2_hidden(B_149,k3_orders_2(A_148,D_151,C_150))
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148)
      | ~ v4_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1457,plain,(
    ! [B_334,C_333,A_332,D_331,A_335] :
      ( r2_orders_2(A_332,'#skF_1'(A_335,B_334),C_333)
      | ~ m1_subset_1(D_331,k1_zfmisc_1(u1_struct_0(A_332)))
      | ~ m1_subset_1(C_333,u1_struct_0(A_332))
      | ~ m1_subset_1('#skF_1'(A_335,B_334),u1_struct_0(A_332))
      | ~ l1_orders_2(A_332)
      | ~ v5_orders_2(A_332)
      | ~ v4_orders_2(A_332)
      | ~ v3_orders_2(A_332)
      | v2_struct_0(A_332)
      | ~ r1_tarski(A_335,k3_orders_2(A_332,D_331,C_333))
      | r1_tarski(A_335,B_334) ) ),
    inference(resolution,[status(thm)],[c_71,c_318])).

tff(c_1461,plain,(
    ! [A_335,B_334,C_333] :
      ( r2_orders_2('#skF_2','#skF_1'(A_335,B_334),C_333)
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_335,B_334),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_335,k3_orders_2('#skF_2','#skF_5',C_333))
      | r1_tarski(A_335,B_334) ) ),
    inference(resolution,[status(thm)],[c_34,c_1457])).

tff(c_1467,plain,(
    ! [A_335,B_334,C_333] :
      ( r2_orders_2('#skF_2','#skF_1'(A_335,B_334),C_333)
      | ~ m1_subset_1(C_333,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_335,B_334),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_335,k3_orders_2('#skF_2','#skF_5',C_333))
      | r1_tarski(A_335,B_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_1461])).

tff(c_1473,plain,(
    ! [A_336,B_337,C_338] :
      ( r2_orders_2('#skF_2','#skF_1'(A_336,B_337),C_338)
      | ~ m1_subset_1(C_338,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_336,B_337),u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_336,k3_orders_2('#skF_2','#skF_5',C_338))
      | r1_tarski(A_336,B_337) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1467])).

tff(c_1513,plain,(
    ! [A_342,B_343,C_344] :
      ( r2_orders_2('#skF_2','#skF_1'(A_342,B_343),C_344)
      | ~ m1_subset_1(C_344,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_342,k3_orders_2('#skF_2','#skF_5',C_344))
      | r1_tarski(A_342,B_343)
      | ~ r2_hidden('#skF_1'(A_342,B_343),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_1473])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_30,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_462,plain,(
    ! [E_177,A_178,D_179,C_180,B_176] :
      ( r2_hidden(B_176,E_177)
      | ~ m1_orders_2(E_177,A_178,D_179)
      | ~ r2_hidden(C_180,E_177)
      | ~ r2_hidden(B_176,D_179)
      | ~ r2_orders_2(A_178,B_176,C_180)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ m1_subset_1(C_180,u1_struct_0(A_178))
      | ~ m1_subset_1(B_176,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v4_orders_2(A_178)
      | ~ v3_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_464,plain,(
    ! [B_176,C_180] :
      ( r2_hidden(B_176,'#skF_4')
      | ~ r2_hidden(C_180,'#skF_4')
      | ~ r2_hidden(B_176,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_176,C_180)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_462])).

tff(c_467,plain,(
    ! [B_176,C_180] :
      ( r2_hidden(B_176,'#skF_4')
      | ~ r2_hidden(C_180,'#skF_4')
      | ~ r2_hidden(B_176,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_176,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_36,c_464])).

tff(c_468,plain,(
    ! [B_176,C_180] :
      ( r2_hidden(B_176,'#skF_4')
      | ~ r2_hidden(C_180,'#skF_4')
      | ~ r2_hidden(B_176,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_176,C_180)
      | ~ m1_subset_1(C_180,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_176,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_467])).

tff(c_1847,plain,(
    ! [A_386,B_387,C_388] :
      ( r2_hidden('#skF_1'(A_386,B_387),'#skF_4')
      | ~ r2_hidden(C_388,'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_386,B_387),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_388,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_386,k3_orders_2('#skF_2','#skF_5',C_388))
      | r1_tarski(A_386,B_387)
      | ~ r2_hidden('#skF_1'(A_386,B_387),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1513,c_468])).

tff(c_1928,plain,(
    ! [A_394,B_395,C_396] :
      ( r2_hidden('#skF_1'(A_394,B_395),'#skF_4')
      | ~ r2_hidden(C_396,'#skF_4')
      | ~ m1_subset_1(C_396,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_394,k3_orders_2('#skF_2','#skF_5',C_396))
      | r1_tarski(A_394,B_395)
      | ~ r2_hidden('#skF_1'(A_394,B_395),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_1847])).

tff(c_1957,plain,(
    ! [C_397,B_398] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_397),B_398),'#skF_4')
      | ~ r2_hidden(C_397,'#skF_4')
      | ~ m1_subset_1(C_397,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_397),B_398)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_397),B_398),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_1928])).

tff(c_1977,plain,(
    ! [C_208,B_209] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_208),B_209),'#skF_4')
      | ~ r2_hidden(C_208,'#skF_4')
      | ~ r1_tarski('#skF_5','#skF_5')
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_532,c_1957])).

tff(c_2007,plain,(
    ! [C_208,B_209] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_208),B_209),'#skF_4')
      | ~ r2_hidden(C_208,'#skF_4')
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),B_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1977])).

tff(c_269,plain,(
    ! [A_136,B_137,C_138,B_2] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_136,B_137,C_138),B_2),u1_struct_0(A_136))
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136)
      | ~ v4_orders_2(A_136)
      | ~ v3_orders_2(A_136)
      | v2_struct_0(A_136)
      | r1_tarski(k3_orders_2(A_136,B_137,C_138),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_249])).

tff(c_87,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_91,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_81])).

tff(c_621,plain,(
    ! [A_224,D_225,C_226,B_227] :
      ( r2_orders_2(A_224,'#skF_1'(k3_orders_2(A_224,D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_subset_1(C_226,u1_struct_0(A_224))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_224,D_225,C_226),B_227),u1_struct_0(A_224))
      | ~ l1_orders_2(A_224)
      | ~ v5_orders_2(A_224)
      | ~ v4_orders_2(A_224)
      | ~ v3_orders_2(A_224)
      | v2_struct_0(A_224)
      | r1_tarski(k3_orders_2(A_224,D_225,C_226),B_227) ) ),
    inference(resolution,[status(thm)],[c_6,c_318])).

tff(c_630,plain,(
    ! [D_225,C_226,B_227] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_225,C_226),B_227)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_87,c_621])).

tff(c_645,plain,(
    ! [D_225,C_226,B_227] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_225,C_226),B_227)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_630])).

tff(c_1111,plain,(
    ! [D_287,C_288,B_289] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_287,C_288),B_289),C_288)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_288,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2',D_287,C_288),B_289)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_287,C_288),B_289),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_645])).

tff(c_339,plain,(
    ! [B_152,A_153,D_154,C_155] :
      ( r2_hidden(B_152,k3_orders_2(A_153,D_154,C_155))
      | ~ r2_hidden(B_152,D_154)
      | ~ r2_orders_2(A_153,B_152,C_155)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_152,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v5_orders_2(A_153)
      | ~ v4_orders_2(A_153)
      | ~ v3_orders_2(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_345,plain,(
    ! [B_152,C_155] :
      ( r2_hidden(B_152,k3_orders_2('#skF_2','#skF_4',C_155))
      | ~ r2_hidden(B_152,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_152,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_339])).

tff(c_353,plain,(
    ! [B_152,C_155] :
      ( r2_hidden(B_152,k3_orders_2('#skF_2','#skF_4',C_155))
      | ~ r2_hidden(B_152,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_152,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_345])).

tff(c_382,plain,(
    ! [B_158,C_159] :
      ( r2_hidden(B_158,k3_orders_2('#skF_2','#skF_4',C_159))
      | ~ r2_hidden(B_158,'#skF_4')
      | ~ r2_orders_2('#skF_2',B_158,C_159)
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_353])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,(
    ! [A_1,C_159] :
      ( r1_tarski(A_1,k3_orders_2('#skF_2','#skF_4',C_159))
      | ~ r2_hidden('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_4',C_159)),'#skF_4')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_1,k3_orders_2('#skF_2','#skF_4',C_159)),C_159)
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_1,k3_orders_2('#skF_2','#skF_4',C_159)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_382,c_4])).

tff(c_3717,plain,(
    ! [D_517,C_518] :
      ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_517,C_518),k3_orders_2('#skF_2','#skF_4',C_518)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_517,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_518,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2',D_517,C_518),k3_orders_2('#skF_2','#skF_4',C_518))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_517,C_518),k3_orders_2('#skF_2','#skF_4',C_518)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1111,c_408])).

tff(c_3729,plain,(
    ! [B_137,C_138] :
      ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_137,C_138),k3_orders_2('#skF_2','#skF_4',C_138)),'#skF_4')
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',B_137,C_138),k3_orders_2('#skF_2','#skF_4',C_138)) ) ),
    inference(resolution,[status(thm)],[c_269,c_3717])).

tff(c_3744,plain,(
    ! [B_137,C_138] :
      ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_137,C_138),k3_orders_2('#skF_2','#skF_4',C_138)),'#skF_4')
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',B_137,C_138),k3_orders_2('#skF_2','#skF_4',C_138)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_3729])).

tff(c_3788,plain,(
    ! [B_521,C_522] :
      ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',B_521,C_522),k3_orders_2('#skF_2','#skF_4',C_522)),'#skF_4')
      | ~ m1_subset_1(C_522,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski(k3_orders_2('#skF_2',B_521,C_522),k3_orders_2('#skF_2','#skF_4',C_522)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3744])).

tff(c_3800,plain,(
    ! [C_208] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(C_208,'#skF_4')
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),k3_orders_2('#skF_2','#skF_4',C_208)) ) ),
    inference(resolution,[status(thm)],[c_2007,c_3788])).

tff(c_3848,plain,(
    ! [C_208] :
      ( ~ r2_hidden(C_208,'#skF_4')
      | ~ m1_subset_1(C_208,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_5',C_208),k3_orders_2('#skF_2','#skF_4',C_208)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3800])).

tff(c_103,plain,(
    ! [C_103,B_104,A_105] :
      ( r1_tarski(C_103,B_104)
      | ~ m1_orders_2(C_103,A_105,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_orders_2(A_105)
      | ~ v5_orders_2(A_105)
      | ~ v4_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_105,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_108,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_34,c_105])).

tff(c_109,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_108])).

tff(c_480,plain,(
    ! [A_194,B_192,C_191] :
      ( m1_subset_1('#skF_1'(A_194,B_192),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_194,k3_orders_2('#skF_2','#skF_4',C_191))
      | r1_tarski(A_194,B_192) ) ),
    inference(resolution,[status(thm)],[c_36,c_474])).

tff(c_488,plain,(
    ! [A_194,B_192,C_191] :
      ( m1_subset_1('#skF_1'(A_194,B_192),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_194,k3_orders_2('#skF_2','#skF_4',C_191))
      | r1_tarski(A_194,B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_480])).

tff(c_495,plain,(
    ! [A_199,B_200,C_201] :
      ( m1_subset_1('#skF_1'(A_199,B_200),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_199,k3_orders_2('#skF_2','#skF_4',C_201))
      | r1_tarski(A_199,B_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_488])).

tff(c_573,plain,(
    ! [C_218,B_219] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_218),B_219),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_218),B_219) ) ),
    inference(resolution,[status(thm)],[c_12,c_495])).

tff(c_203,plain,(
    ! [A_121,D_120,C_122,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_121,D_120,C_122),B_2),D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(u1_struct_0(A_121)))
      | ~ m1_subset_1(C_122,u1_struct_0(A_121))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_121,D_120,C_122),B_2),u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121)
      | r1_tarski(k3_orders_2(A_121,D_120,C_122),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_183])).

tff(c_575,plain,(
    ! [C_218,B_219] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_218),B_219),'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_218),B_219) ) ),
    inference(resolution,[status(thm)],[c_573,c_203])).

tff(c_578,plain,(
    ! [C_218,B_219] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_218),B_219),'#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_218,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_218),B_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_36,c_575])).

tff(c_580,plain,(
    ! [C_220,B_221] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_220),B_221),'#skF_4')
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_220),B_221) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_578])).

tff(c_592,plain,(
    ! [C_220,B_221,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_220),B_221),B_2)
      | ~ r1_tarski('#skF_4',B_2)
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_220),B_221) ) ),
    inference(resolution,[status(thm)],[c_580,c_2])).

tff(c_499,plain,(
    ! [C_201,B_200] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_201),B_200),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_201),B_200) ) ),
    inference(resolution,[status(thm)],[c_12,c_495])).

tff(c_633,plain,(
    ! [D_225,C_226,B_227] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_225,C_226),B_227)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_86,c_621])).

tff(c_649,plain,(
    ! [D_225,C_226,B_227] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k3_orders_2('#skF_2',D_225,C_226),B_227)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_633])).

tff(c_650,plain,(
    ! [D_225,C_226,B_227] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),C_226)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_226,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2',D_225,C_226),B_227)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_225,C_226),B_227),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_649])).

tff(c_343,plain,(
    ! [B_152,C_155] :
      ( r2_hidden(B_152,k3_orders_2('#skF_2','#skF_5',C_155))
      | ~ r2_hidden(B_152,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_152,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_339])).

tff(c_349,plain,(
    ! [B_152,C_155] :
      ( r2_hidden(B_152,k3_orders_2('#skF_2','#skF_5',C_155))
      | ~ r2_hidden(B_152,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_152,C_155)
      | ~ m1_subset_1(C_155,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_343])).

tff(c_355,plain,(
    ! [B_156,C_157] :
      ( r2_hidden(B_156,k3_orders_2('#skF_2','#skF_5',C_157))
      | ~ r2_hidden(B_156,'#skF_5')
      | ~ r2_orders_2('#skF_2',B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_156,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_349])).

tff(c_1229,plain,(
    ! [A_306,C_307] :
      ( r1_tarski(A_306,k3_orders_2('#skF_2','#skF_5',C_307))
      | ~ r2_hidden('#skF_1'(A_306,k3_orders_2('#skF_2','#skF_5',C_307)),'#skF_5')
      | ~ r2_orders_2('#skF_2','#skF_1'(A_306,k3_orders_2('#skF_2','#skF_5',C_307)),C_307)
      | ~ m1_subset_1(C_307,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(A_306,k3_orders_2('#skF_2','#skF_5',C_307)),u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_355,c_4])).

tff(c_3458,plain,(
    ! [D_510,C_511] :
      ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_510,C_511),k3_orders_2('#skF_2','#skF_5',C_511)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_510,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_511,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2',D_510,C_511),k3_orders_2('#skF_2','#skF_5',C_511))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_510,C_511),k3_orders_2('#skF_2','#skF_5',C_511)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_650,c_1229])).

tff(c_3462,plain,(
    ! [C_201] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_201),k3_orders_2('#skF_2','#skF_5',C_201)),'#skF_5')
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_201),k3_orders_2('#skF_2','#skF_5',C_201)) ) ),
    inference(resolution,[status(thm)],[c_499,c_3458])).

tff(c_3489,plain,(
    ! [C_512] :
      ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_4',C_512),k3_orders_2('#skF_2','#skF_5',C_512)),'#skF_5')
      | ~ m1_subset_1(C_512,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_512),k3_orders_2('#skF_2','#skF_5',C_512)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3462])).

tff(c_3509,plain,(
    ! [C_220] :
      ( ~ r1_tarski('#skF_4','#skF_5')
      | ~ m1_subset_1(C_220,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_220),k3_orders_2('#skF_2','#skF_5',C_220)) ) ),
    inference(resolution,[status(thm)],[c_592,c_3489])).

tff(c_3544,plain,(
    ! [C_513] :
      ( ~ m1_subset_1(C_513,u1_struct_0('#skF_2'))
      | r1_tarski(k3_orders_2('#skF_2','#skF_4',C_513),k3_orders_2('#skF_2','#skF_5',C_513)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3509])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3994,plain,(
    ! [C_525] :
      ( k3_orders_2('#skF_2','#skF_5',C_525) = k3_orders_2('#skF_2','#skF_4',C_525)
      | ~ r1_tarski(k3_orders_2('#skF_2','#skF_5',C_525),k3_orders_2('#skF_2','#skF_4',C_525))
      | ~ m1_subset_1(C_525,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3544,c_8])).

tff(c_4009,plain,(
    ! [C_526] :
      ( k3_orders_2('#skF_2','#skF_5',C_526) = k3_orders_2('#skF_2','#skF_4',C_526)
      | ~ r2_hidden(C_526,'#skF_4')
      | ~ m1_subset_1(C_526,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3848,c_3994])).

tff(c_4028,plain,
    ( k3_orders_2('#skF_2','#skF_5','#skF_3') = k3_orders_2('#skF_2','#skF_4','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_4009])).

tff(c_4039,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') = k3_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4028])).

tff(c_4041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_4039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.91/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.49  
% 6.91/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.49  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.91/2.49  
% 6.91/2.49  %Foreground sorts:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Background operators:
% 6.91/2.49  
% 6.91/2.49  
% 6.91/2.49  %Foreground operators:
% 6.91/2.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.91/2.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.91/2.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.91/2.49  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 6.91/2.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.91/2.49  tff('#skF_5', type, '#skF_5': $i).
% 6.91/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.91/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.91/2.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.91/2.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.91/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.91/2.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.91/2.49  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 6.91/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.91/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.91/2.49  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.91/2.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.91/2.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.91/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.91/2.49  
% 7.31/2.51  tff(f_166, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, C) & m1_orders_2(C, A, D)) => (k3_orders_2(A, C, B) = k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_orders_2)).
% 7.31/2.51  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.31/2.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.31/2.51  tff(f_61, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 7.31/2.51  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.31/2.51  tff(f_87, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 7.31/2.51  tff(f_139, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_orders_2)).
% 7.31/2.51  tff(f_106, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 7.31/2.51  tff(c_28, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k3_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_32, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.31/2.51  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_46, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_44, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_42, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_40, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.51  tff(c_66, plain, (![C_85, B_86, A_87]: (r2_hidden(C_85, B_86) | ~r2_hidden(C_85, A_87) | ~r1_tarski(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.51  tff(c_71, plain, (![A_1, B_2, B_86]: (r2_hidden('#skF_1'(A_1, B_2), B_86) | ~r1_tarski(A_1, B_86) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_66])).
% 7.31/2.51  tff(c_121, plain, (![A_106, B_107, C_108]: (m1_subset_1(k3_orders_2(A_106, B_107, C_108), k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.31/2.51  tff(c_14, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.31/2.51  tff(c_249, plain, (![A_135, A_136, B_137, C_138]: (m1_subset_1(A_135, u1_struct_0(A_136)) | ~r2_hidden(A_135, k3_orders_2(A_136, B_137, C_138)) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_121, c_14])).
% 7.31/2.51  tff(c_474, plain, (![A_195, B_192, A_194, C_191, B_193]: (m1_subset_1('#skF_1'(A_194, B_192), u1_struct_0(A_195)) | ~m1_subset_1(C_191, u1_struct_0(A_195)) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_orders_2(A_195) | ~v5_orders_2(A_195) | ~v4_orders_2(A_195) | ~v3_orders_2(A_195) | v2_struct_0(A_195) | ~r1_tarski(A_194, k3_orders_2(A_195, B_193, C_191)) | r1_tarski(A_194, B_192))), inference(resolution, [status(thm)], [c_71, c_249])).
% 7.31/2.51  tff(c_478, plain, (![A_194, B_192, C_191]: (m1_subset_1('#skF_1'(A_194, B_192), u1_struct_0('#skF_2')) | ~m1_subset_1(C_191, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_194, k3_orders_2('#skF_2', '#skF_5', C_191)) | r1_tarski(A_194, B_192))), inference(resolution, [status(thm)], [c_34, c_474])).
% 7.31/2.51  tff(c_484, plain, (![A_194, B_192, C_191]: (m1_subset_1('#skF_1'(A_194, B_192), u1_struct_0('#skF_2')) | ~m1_subset_1(C_191, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_194, k3_orders_2('#skF_2', '#skF_5', C_191)) | r1_tarski(A_194, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_478])).
% 7.31/2.51  tff(c_490, plain, (![A_196, B_197, C_198]: (m1_subset_1('#skF_1'(A_196, B_197), u1_struct_0('#skF_2')) | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | ~r1_tarski(A_196, k3_orders_2('#skF_2', '#skF_5', C_198)) | r1_tarski(A_196, B_197))), inference(negUnitSimplification, [status(thm)], [c_48, c_484])).
% 7.31/2.51  tff(c_494, plain, (![C_198, B_197]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198), B_197), u1_struct_0('#skF_2')) | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_198), B_197))), inference(resolution, [status(thm)], [c_12, c_490])).
% 7.31/2.51  tff(c_183, plain, (![B_119, D_120, A_121, C_122]: (r2_hidden(B_119, D_120) | ~r2_hidden(B_119, k3_orders_2(A_121, D_120, C_122)) | ~m1_subset_1(D_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_subset_1(C_122, u1_struct_0(A_121)) | ~m1_subset_1(B_119, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.51  tff(c_501, plain, (![A_204, D_205, C_206, B_207]: (r2_hidden('#skF_1'(k3_orders_2(A_204, D_205, C_206), B_207), D_205) | ~m1_subset_1(D_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(C_206, u1_struct_0(A_204)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_204, D_205, C_206), B_207), u1_struct_0(A_204)) | ~l1_orders_2(A_204) | ~v5_orders_2(A_204) | ~v4_orders_2(A_204) | ~v3_orders_2(A_204) | v2_struct_0(A_204) | r1_tarski(k3_orders_2(A_204, D_205, C_206), B_207))), inference(resolution, [status(thm)], [c_6, c_183])).
% 7.31/2.51  tff(c_503, plain, (![C_198, B_197]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198), B_197), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_198), B_197))), inference(resolution, [status(thm)], [c_494, c_501])).
% 7.31/2.51  tff(c_514, plain, (![C_198, B_197]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_198), B_197), '#skF_5') | v2_struct_0('#skF_2') | ~m1_subset_1(C_198, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_198), B_197))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_503])).
% 7.31/2.51  tff(c_525, plain, (![C_208, B_209]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_208), B_209), '#skF_5') | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), B_209))), inference(negUnitSimplification, [status(thm)], [c_48, c_514])).
% 7.31/2.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.51  tff(c_532, plain, (![C_208, B_209, B_2]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_208), B_209), B_2) | ~r1_tarski('#skF_5', B_2) | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), B_209))), inference(resolution, [status(thm)], [c_525, c_2])).
% 7.31/2.51  tff(c_81, plain, (![A_91, C_92, B_93]: (m1_subset_1(A_91, C_92) | ~m1_subset_1(B_93, k1_zfmisc_1(C_92)) | ~r2_hidden(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.31/2.51  tff(c_86, plain, (![A_91]: (m1_subset_1(A_91, u1_struct_0('#skF_2')) | ~r2_hidden(A_91, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_81])).
% 7.31/2.51  tff(c_318, plain, (![A_148, B_149, C_150, D_151]: (r2_orders_2(A_148, B_149, C_150) | ~r2_hidden(B_149, k3_orders_2(A_148, D_151, C_150)) | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0(A_148))) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148) | ~v4_orders_2(A_148) | ~v3_orders_2(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.51  tff(c_1457, plain, (![B_334, C_333, A_332, D_331, A_335]: (r2_orders_2(A_332, '#skF_1'(A_335, B_334), C_333) | ~m1_subset_1(D_331, k1_zfmisc_1(u1_struct_0(A_332))) | ~m1_subset_1(C_333, u1_struct_0(A_332)) | ~m1_subset_1('#skF_1'(A_335, B_334), u1_struct_0(A_332)) | ~l1_orders_2(A_332) | ~v5_orders_2(A_332) | ~v4_orders_2(A_332) | ~v3_orders_2(A_332) | v2_struct_0(A_332) | ~r1_tarski(A_335, k3_orders_2(A_332, D_331, C_333)) | r1_tarski(A_335, B_334))), inference(resolution, [status(thm)], [c_71, c_318])).
% 7.31/2.51  tff(c_1461, plain, (![A_335, B_334, C_333]: (r2_orders_2('#skF_2', '#skF_1'(A_335, B_334), C_333) | ~m1_subset_1(C_333, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_335, B_334), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_335, k3_orders_2('#skF_2', '#skF_5', C_333)) | r1_tarski(A_335, B_334))), inference(resolution, [status(thm)], [c_34, c_1457])).
% 7.31/2.51  tff(c_1467, plain, (![A_335, B_334, C_333]: (r2_orders_2('#skF_2', '#skF_1'(A_335, B_334), C_333) | ~m1_subset_1(C_333, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_335, B_334), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_335, k3_orders_2('#skF_2', '#skF_5', C_333)) | r1_tarski(A_335, B_334))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_1461])).
% 7.31/2.51  tff(c_1473, plain, (![A_336, B_337, C_338]: (r2_orders_2('#skF_2', '#skF_1'(A_336, B_337), C_338) | ~m1_subset_1(C_338, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_336, B_337), u1_struct_0('#skF_2')) | ~r1_tarski(A_336, k3_orders_2('#skF_2', '#skF_5', C_338)) | r1_tarski(A_336, B_337))), inference(negUnitSimplification, [status(thm)], [c_48, c_1467])).
% 7.31/2.51  tff(c_1513, plain, (![A_342, B_343, C_344]: (r2_orders_2('#skF_2', '#skF_1'(A_342, B_343), C_344) | ~m1_subset_1(C_344, u1_struct_0('#skF_2')) | ~r1_tarski(A_342, k3_orders_2('#skF_2', '#skF_5', C_344)) | r1_tarski(A_342, B_343) | ~r2_hidden('#skF_1'(A_342, B_343), '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_1473])).
% 7.31/2.51  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_30, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 7.31/2.51  tff(c_462, plain, (![E_177, A_178, D_179, C_180, B_176]: (r2_hidden(B_176, E_177) | ~m1_orders_2(E_177, A_178, D_179) | ~r2_hidden(C_180, E_177) | ~r2_hidden(B_176, D_179) | ~r2_orders_2(A_178, B_176, C_180) | ~m1_subset_1(E_177, k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(D_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~m1_subset_1(C_180, u1_struct_0(A_178)) | ~m1_subset_1(B_176, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v5_orders_2(A_178) | ~v4_orders_2(A_178) | ~v3_orders_2(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.31/2.51  tff(c_464, plain, (![B_176, C_180]: (r2_hidden(B_176, '#skF_4') | ~r2_hidden(C_180, '#skF_4') | ~r2_hidden(B_176, '#skF_5') | ~r2_orders_2('#skF_2', B_176, C_180) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_180, u1_struct_0('#skF_2')) | ~m1_subset_1(B_176, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_462])).
% 7.31/2.51  tff(c_467, plain, (![B_176, C_180]: (r2_hidden(B_176, '#skF_4') | ~r2_hidden(C_180, '#skF_4') | ~r2_hidden(B_176, '#skF_5') | ~r2_orders_2('#skF_2', B_176, C_180) | ~m1_subset_1(C_180, u1_struct_0('#skF_2')) | ~m1_subset_1(B_176, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_36, c_464])).
% 7.31/2.51  tff(c_468, plain, (![B_176, C_180]: (r2_hidden(B_176, '#skF_4') | ~r2_hidden(C_180, '#skF_4') | ~r2_hidden(B_176, '#skF_5') | ~r2_orders_2('#skF_2', B_176, C_180) | ~m1_subset_1(C_180, u1_struct_0('#skF_2')) | ~m1_subset_1(B_176, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_467])).
% 7.31/2.51  tff(c_1847, plain, (![A_386, B_387, C_388]: (r2_hidden('#skF_1'(A_386, B_387), '#skF_4') | ~r2_hidden(C_388, '#skF_4') | ~m1_subset_1('#skF_1'(A_386, B_387), u1_struct_0('#skF_2')) | ~m1_subset_1(C_388, u1_struct_0('#skF_2')) | ~r1_tarski(A_386, k3_orders_2('#skF_2', '#skF_5', C_388)) | r1_tarski(A_386, B_387) | ~r2_hidden('#skF_1'(A_386, B_387), '#skF_5'))), inference(resolution, [status(thm)], [c_1513, c_468])).
% 7.31/2.51  tff(c_1928, plain, (![A_394, B_395, C_396]: (r2_hidden('#skF_1'(A_394, B_395), '#skF_4') | ~r2_hidden(C_396, '#skF_4') | ~m1_subset_1(C_396, u1_struct_0('#skF_2')) | ~r1_tarski(A_394, k3_orders_2('#skF_2', '#skF_5', C_396)) | r1_tarski(A_394, B_395) | ~r2_hidden('#skF_1'(A_394, B_395), '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_1847])).
% 7.31/2.51  tff(c_1957, plain, (![C_397, B_398]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_397), B_398), '#skF_4') | ~r2_hidden(C_397, '#skF_4') | ~m1_subset_1(C_397, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_397), B_398) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_397), B_398), '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_1928])).
% 7.31/2.51  tff(c_1977, plain, (![C_208, B_209]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_208), B_209), '#skF_4') | ~r2_hidden(C_208, '#skF_4') | ~r1_tarski('#skF_5', '#skF_5') | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), B_209))), inference(resolution, [status(thm)], [c_532, c_1957])).
% 7.31/2.51  tff(c_2007, plain, (![C_208, B_209]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_208), B_209), '#skF_4') | ~r2_hidden(C_208, '#skF_4') | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), B_209))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1977])).
% 7.31/2.51  tff(c_269, plain, (![A_136, B_137, C_138, B_2]: (m1_subset_1('#skF_1'(k3_orders_2(A_136, B_137, C_138), B_2), u1_struct_0(A_136)) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136) | ~v4_orders_2(A_136) | ~v3_orders_2(A_136) | v2_struct_0(A_136) | r1_tarski(k3_orders_2(A_136, B_137, C_138), B_2))), inference(resolution, [status(thm)], [c_6, c_249])).
% 7.31/2.51  tff(c_87, plain, (![A_91]: (m1_subset_1(A_91, u1_struct_0('#skF_2')) | ~r2_hidden(A_91, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_81])).
% 7.31/2.51  tff(c_621, plain, (![A_224, D_225, C_226, B_227]: (r2_orders_2(A_224, '#skF_1'(k3_orders_2(A_224, D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_subset_1(C_226, u1_struct_0(A_224)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_224, D_225, C_226), B_227), u1_struct_0(A_224)) | ~l1_orders_2(A_224) | ~v5_orders_2(A_224) | ~v4_orders_2(A_224) | ~v3_orders_2(A_224) | v2_struct_0(A_224) | r1_tarski(k3_orders_2(A_224, D_225, C_226), B_227))), inference(resolution, [status(thm)], [c_6, c_318])).
% 7.31/2.51  tff(c_630, plain, (![D_225, C_226, B_227]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_226, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_225, C_226), B_227) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_621])).
% 7.31/2.51  tff(c_645, plain, (![D_225, C_226, B_227]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_226, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_225, C_226), B_227) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_630])).
% 7.31/2.51  tff(c_1111, plain, (![D_287, C_288, B_289]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_287, C_288), B_289), C_288) | ~m1_subset_1(D_287, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_288, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', D_287, C_288), B_289) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_287, C_288), B_289), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_645])).
% 7.31/2.51  tff(c_339, plain, (![B_152, A_153, D_154, C_155]: (r2_hidden(B_152, k3_orders_2(A_153, D_154, C_155)) | ~r2_hidden(B_152, D_154) | ~r2_orders_2(A_153, B_152, C_155) | ~m1_subset_1(D_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_152, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v5_orders_2(A_153) | ~v4_orders_2(A_153) | ~v3_orders_2(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.51  tff(c_345, plain, (![B_152, C_155]: (r2_hidden(B_152, k3_orders_2('#skF_2', '#skF_4', C_155)) | ~r2_hidden(B_152, '#skF_4') | ~r2_orders_2('#skF_2', B_152, C_155) | ~m1_subset_1(C_155, u1_struct_0('#skF_2')) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_339])).
% 7.31/2.51  tff(c_353, plain, (![B_152, C_155]: (r2_hidden(B_152, k3_orders_2('#skF_2', '#skF_4', C_155)) | ~r2_hidden(B_152, '#skF_4') | ~r2_orders_2('#skF_2', B_152, C_155) | ~m1_subset_1(C_155, u1_struct_0('#skF_2')) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_345])).
% 7.31/2.51  tff(c_382, plain, (![B_158, C_159]: (r2_hidden(B_158, k3_orders_2('#skF_2', '#skF_4', C_159)) | ~r2_hidden(B_158, '#skF_4') | ~r2_orders_2('#skF_2', B_158, C_159) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1(B_158, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_353])).
% 7.31/2.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.51  tff(c_408, plain, (![A_1, C_159]: (r1_tarski(A_1, k3_orders_2('#skF_2', '#skF_4', C_159)) | ~r2_hidden('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_4', C_159)), '#skF_4') | ~r2_orders_2('#skF_2', '#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_4', C_159)), C_159) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_1, k3_orders_2('#skF_2', '#skF_4', C_159)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_382, c_4])).
% 7.31/2.51  tff(c_3717, plain, (![D_517, C_518]: (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_517, C_518), k3_orders_2('#skF_2', '#skF_4', C_518)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_517, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_518, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', D_517, C_518), k3_orders_2('#skF_2', '#skF_4', C_518)) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_517, C_518), k3_orders_2('#skF_2', '#skF_4', C_518)), '#skF_4'))), inference(resolution, [status(thm)], [c_1111, c_408])).
% 7.31/2.51  tff(c_3729, plain, (![B_137, C_138]: (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_137, C_138), k3_orders_2('#skF_2', '#skF_4', C_138)), '#skF_4') | ~m1_subset_1(C_138, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', B_137, C_138), k3_orders_2('#skF_2', '#skF_4', C_138)))), inference(resolution, [status(thm)], [c_269, c_3717])).
% 7.31/2.51  tff(c_3744, plain, (![B_137, C_138]: (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_137, C_138), k3_orders_2('#skF_2', '#skF_4', C_138)), '#skF_4') | ~m1_subset_1(C_138, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', B_137, C_138), k3_orders_2('#skF_2', '#skF_4', C_138)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_3729])).
% 7.31/2.51  tff(c_3788, plain, (![B_521, C_522]: (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', B_521, C_522), k3_orders_2('#skF_2', '#skF_4', C_522)), '#skF_4') | ~m1_subset_1(C_522, u1_struct_0('#skF_2')) | ~m1_subset_1(B_521, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski(k3_orders_2('#skF_2', B_521, C_522), k3_orders_2('#skF_2', '#skF_4', C_522)))), inference(negUnitSimplification, [status(thm)], [c_48, c_3744])).
% 7.31/2.51  tff(c_3800, plain, (![C_208]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(C_208, '#skF_4') | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), k3_orders_2('#skF_2', '#skF_4', C_208)))), inference(resolution, [status(thm)], [c_2007, c_3788])).
% 7.31/2.51  tff(c_3848, plain, (![C_208]: (~r2_hidden(C_208, '#skF_4') | ~m1_subset_1(C_208, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_208), k3_orders_2('#skF_2', '#skF_4', C_208)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3800])).
% 7.31/2.51  tff(c_103, plain, (![C_103, B_104, A_105]: (r1_tarski(C_103, B_104) | ~m1_orders_2(C_103, A_105, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_orders_2(A_105) | ~v5_orders_2(A_105) | ~v4_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.31/2.51  tff(c_105, plain, (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_103])).
% 7.31/2.51  tff(c_108, plain, (r1_tarski('#skF_4', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_34, c_105])).
% 7.31/2.51  tff(c_109, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_108])).
% 7.31/2.51  tff(c_480, plain, (![A_194, B_192, C_191]: (m1_subset_1('#skF_1'(A_194, B_192), u1_struct_0('#skF_2')) | ~m1_subset_1(C_191, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_194, k3_orders_2('#skF_2', '#skF_4', C_191)) | r1_tarski(A_194, B_192))), inference(resolution, [status(thm)], [c_36, c_474])).
% 7.31/2.51  tff(c_488, plain, (![A_194, B_192, C_191]: (m1_subset_1('#skF_1'(A_194, B_192), u1_struct_0('#skF_2')) | ~m1_subset_1(C_191, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~r1_tarski(A_194, k3_orders_2('#skF_2', '#skF_4', C_191)) | r1_tarski(A_194, B_192))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_480])).
% 7.31/2.51  tff(c_495, plain, (![A_199, B_200, C_201]: (m1_subset_1('#skF_1'(A_199, B_200), u1_struct_0('#skF_2')) | ~m1_subset_1(C_201, u1_struct_0('#skF_2')) | ~r1_tarski(A_199, k3_orders_2('#skF_2', '#skF_4', C_201)) | r1_tarski(A_199, B_200))), inference(negUnitSimplification, [status(thm)], [c_48, c_488])).
% 7.31/2.51  tff(c_573, plain, (![C_218, B_219]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_218), B_219), u1_struct_0('#skF_2')) | ~m1_subset_1(C_218, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_218), B_219))), inference(resolution, [status(thm)], [c_12, c_495])).
% 7.31/2.51  tff(c_203, plain, (![A_121, D_120, C_122, B_2]: (r2_hidden('#skF_1'(k3_orders_2(A_121, D_120, C_122), B_2), D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(u1_struct_0(A_121))) | ~m1_subset_1(C_122, u1_struct_0(A_121)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_121, D_120, C_122), B_2), u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121) | r1_tarski(k3_orders_2(A_121, D_120, C_122), B_2))), inference(resolution, [status(thm)], [c_6, c_183])).
% 7.31/2.51  tff(c_575, plain, (![C_218, B_219]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_218), B_219), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_218, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_218), B_219))), inference(resolution, [status(thm)], [c_573, c_203])).
% 7.31/2.51  tff(c_578, plain, (![C_218, B_219]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_218), B_219), '#skF_4') | v2_struct_0('#skF_2') | ~m1_subset_1(C_218, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_218), B_219))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_36, c_575])).
% 7.31/2.51  tff(c_580, plain, (![C_220, B_221]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_220), B_221), '#skF_4') | ~m1_subset_1(C_220, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_220), B_221))), inference(negUnitSimplification, [status(thm)], [c_48, c_578])).
% 7.31/2.51  tff(c_592, plain, (![C_220, B_221, B_2]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_220), B_221), B_2) | ~r1_tarski('#skF_4', B_2) | ~m1_subset_1(C_220, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_220), B_221))), inference(resolution, [status(thm)], [c_580, c_2])).
% 7.31/2.51  tff(c_499, plain, (![C_201, B_200]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_201), B_200), u1_struct_0('#skF_2')) | ~m1_subset_1(C_201, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_201), B_200))), inference(resolution, [status(thm)], [c_12, c_495])).
% 7.31/2.51  tff(c_633, plain, (![D_225, C_226, B_227]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_226, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_225, C_226), B_227) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), '#skF_5'))), inference(resolution, [status(thm)], [c_86, c_621])).
% 7.31/2.51  tff(c_649, plain, (![D_225, C_226, B_227]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_226, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | r1_tarski(k3_orders_2('#skF_2', D_225, C_226), B_227) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_633])).
% 7.31/2.51  tff(c_650, plain, (![D_225, C_226, B_227]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), C_226) | ~m1_subset_1(D_225, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_226, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', D_225, C_226), B_227) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_225, C_226), B_227), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_649])).
% 7.31/2.51  tff(c_343, plain, (![B_152, C_155]: (r2_hidden(B_152, k3_orders_2('#skF_2', '#skF_5', C_155)) | ~r2_hidden(B_152, '#skF_5') | ~r2_orders_2('#skF_2', B_152, C_155) | ~m1_subset_1(C_155, u1_struct_0('#skF_2')) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_339])).
% 7.31/2.51  tff(c_349, plain, (![B_152, C_155]: (r2_hidden(B_152, k3_orders_2('#skF_2', '#skF_5', C_155)) | ~r2_hidden(B_152, '#skF_5') | ~r2_orders_2('#skF_2', B_152, C_155) | ~m1_subset_1(C_155, u1_struct_0('#skF_2')) | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_343])).
% 7.31/2.51  tff(c_355, plain, (![B_156, C_157]: (r2_hidden(B_156, k3_orders_2('#skF_2', '#skF_5', C_157)) | ~r2_hidden(B_156, '#skF_5') | ~r2_orders_2('#skF_2', B_156, C_157) | ~m1_subset_1(C_157, u1_struct_0('#skF_2')) | ~m1_subset_1(B_156, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_48, c_349])).
% 7.31/2.51  tff(c_1229, plain, (![A_306, C_307]: (r1_tarski(A_306, k3_orders_2('#skF_2', '#skF_5', C_307)) | ~r2_hidden('#skF_1'(A_306, k3_orders_2('#skF_2', '#skF_5', C_307)), '#skF_5') | ~r2_orders_2('#skF_2', '#skF_1'(A_306, k3_orders_2('#skF_2', '#skF_5', C_307)), C_307) | ~m1_subset_1(C_307, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(A_306, k3_orders_2('#skF_2', '#skF_5', C_307)), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_355, c_4])).
% 7.31/2.51  tff(c_3458, plain, (![D_510, C_511]: (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_510, C_511), k3_orders_2('#skF_2', '#skF_5', C_511)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_510, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_511, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', D_510, C_511), k3_orders_2('#skF_2', '#skF_5', C_511)) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_510, C_511), k3_orders_2('#skF_2', '#skF_5', C_511)), '#skF_5'))), inference(resolution, [status(thm)], [c_650, c_1229])).
% 7.31/2.51  tff(c_3462, plain, (![C_201]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_201), k3_orders_2('#skF_2', '#skF_5', C_201)), '#skF_5') | ~m1_subset_1(C_201, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_201), k3_orders_2('#skF_2', '#skF_5', C_201)))), inference(resolution, [status(thm)], [c_499, c_3458])).
% 7.31/2.51  tff(c_3489, plain, (![C_512]: (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_4', C_512), k3_orders_2('#skF_2', '#skF_5', C_512)), '#skF_5') | ~m1_subset_1(C_512, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_512), k3_orders_2('#skF_2', '#skF_5', C_512)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3462])).
% 7.31/2.51  tff(c_3509, plain, (![C_220]: (~r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1(C_220, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_220), k3_orders_2('#skF_2', '#skF_5', C_220)))), inference(resolution, [status(thm)], [c_592, c_3489])).
% 7.31/2.51  tff(c_3544, plain, (![C_513]: (~m1_subset_1(C_513, u1_struct_0('#skF_2')) | r1_tarski(k3_orders_2('#skF_2', '#skF_4', C_513), k3_orders_2('#skF_2', '#skF_5', C_513)))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_3509])).
% 7.31/2.51  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.31/2.51  tff(c_3994, plain, (![C_525]: (k3_orders_2('#skF_2', '#skF_5', C_525)=k3_orders_2('#skF_2', '#skF_4', C_525) | ~r1_tarski(k3_orders_2('#skF_2', '#skF_5', C_525), k3_orders_2('#skF_2', '#skF_4', C_525)) | ~m1_subset_1(C_525, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3544, c_8])).
% 7.31/2.51  tff(c_4009, plain, (![C_526]: (k3_orders_2('#skF_2', '#skF_5', C_526)=k3_orders_2('#skF_2', '#skF_4', C_526) | ~r2_hidden(C_526, '#skF_4') | ~m1_subset_1(C_526, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_3848, c_3994])).
% 7.31/2.51  tff(c_4028, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k3_orders_2('#skF_2', '#skF_4', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_4009])).
% 7.31/2.51  tff(c_4039, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k3_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4028])).
% 7.31/2.51  tff(c_4041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_4039])).
% 7.31/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.51  
% 7.31/2.51  Inference rules
% 7.31/2.51  ----------------------
% 7.31/2.51  #Ref     : 0
% 7.31/2.51  #Sup     : 873
% 7.31/2.51  #Fact    : 0
% 7.31/2.51  #Define  : 0
% 7.31/2.51  #Split   : 3
% 7.31/2.51  #Chain   : 0
% 7.31/2.51  #Close   : 0
% 7.31/2.51  
% 7.31/2.51  Ordering : KBO
% 7.31/2.51  
% 7.31/2.51  Simplification rules
% 7.31/2.51  ----------------------
% 7.31/2.51  #Subsume      : 402
% 7.31/2.51  #Demod        : 568
% 7.31/2.51  #Tautology    : 83
% 7.31/2.51  #SimpNegUnit  : 80
% 7.31/2.51  #BackRed      : 0
% 7.31/2.51  
% 7.31/2.51  #Partial instantiations: 0
% 7.31/2.51  #Strategies tried      : 1
% 7.31/2.51  
% 7.31/2.51  Timing (in seconds)
% 7.31/2.51  ----------------------
% 7.31/2.52  Preprocessing        : 0.36
% 7.31/2.52  Parsing              : 0.19
% 7.31/2.52  CNF conversion       : 0.03
% 7.31/2.52  Main loop            : 1.30
% 7.31/2.52  Inferencing          : 0.38
% 7.31/2.52  Reduction            : 0.33
% 7.31/2.52  Demodulation         : 0.22
% 7.31/2.52  BG Simplification    : 0.04
% 7.31/2.52  Subsumption          : 0.50
% 7.31/2.52  Abstraction          : 0.04
% 7.31/2.52  MUC search           : 0.00
% 7.31/2.52  Cooper               : 0.00
% 7.31/2.52  Total                : 1.71
% 7.31/2.52  Index Insertion      : 0.00
% 7.31/2.52  Index Deletion       : 0.00
% 7.31/2.52  Index Matching       : 0.00
% 7.31/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
