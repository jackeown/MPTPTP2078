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
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 402 expanded)
%              Number of leaves         :   43 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  333 (1784 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_245,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(C))
                     => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_117,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ r2_hidden(C,B)
               => r1_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_163,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_221,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_137,plain,(
    ! [B_141,A_142] :
      ( v2_pre_topc(B_141)
      | ~ m1_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_140,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_137])).

tff(c_143,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_140])).

tff(c_71,plain,(
    ! [B_123,A_124] :
      ( l1_pre_topc(B_123)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_77,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_74])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_446,plain,(
    ! [B_213,A_214] :
      ( r2_hidden(B_213,k1_connsp_2(A_214,B_213))
      | ~ m1_subset_1(B_213,u1_struct_0(A_214))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_451,plain,(
    ! [A_215,B_216] :
      ( ~ v1_xboole_0(k1_connsp_2(A_215,B_216))
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_446,c_2])).

tff(c_454,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_451])).

tff(c_457,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_77,c_454])).

tff(c_458,plain,(
    ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_457])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_261,plain,(
    ! [C_164,A_165,B_166] :
      ( m1_subset_1(C_164,u1_struct_0(A_165))
      | ~ m1_subset_1(C_164,u1_struct_0(B_166))
      | ~ m1_pre_topc(B_166,A_165)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_263,plain,(
    ! [A_165] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_165))
      | ~ m1_pre_topc('#skF_5',A_165)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_50,c_261])).

tff(c_266,plain,(
    ! [A_165] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_165))
      | ~ m1_pre_topc('#skF_5',A_165)
      | ~ l1_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_263])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    r1_xboole_0(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_101,plain,(
    ! [A_137,B_138,C_139] :
      ( ~ r1_xboole_0(A_137,B_138)
      | ~ r2_hidden(C_139,B_138)
      | ~ r2_hidden(C_139,A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [C_140] :
      ( ~ r2_hidden(C_140,'#skF_4')
      | ~ r2_hidden(C_140,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_129,plain,(
    ! [A_13] :
      ( ~ r2_hidden(A_13,'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_13,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_146,plain,(
    ! [A_143] :
      ( ~ r2_hidden(A_143,'#skF_4')
      | ~ m1_subset_1(A_143,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_150,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_44,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_tmap_1(A_39,k6_tmap_1(A_39,B_43),k7_tmap_1(A_39,B_43),C_45)
      | r2_hidden(C_45,B_43)
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_34,plain,(
    ! [A_35,B_36] :
      ( v1_funct_2(k7_tmap_1(A_35,B_36),u1_struct_0(A_35),u1_struct_0(k6_tmap_1(A_35,B_36)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_219,plain,(
    ! [A_156,B_157] :
      ( ~ v2_struct_0(k6_tmap_1(A_156,B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_222,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_219])).

tff(c_225,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_222])).

tff(c_226,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_225])).

tff(c_190,plain,(
    ! [A_148,B_149] :
      ( v2_pre_topc(k6_tmap_1(A_148,B_149))
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_193,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_190])).

tff(c_196,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_193])).

tff(c_197,plain,(
    v2_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_196])).

tff(c_167,plain,(
    ! [A_145,B_146] :
      ( l1_pre_topc(k6_tmap_1(A_145,B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_170,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_167])).

tff(c_173,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_170])).

tff(c_174,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_173])).

tff(c_198,plain,(
    ! [A_150,B_151] :
      ( v1_funct_1(k7_tmap_1(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_201,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_198])).

tff(c_204,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_201])).

tff(c_205,plain,(
    v1_funct_1(k7_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_204])).

tff(c_32,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k7_tmap_1(A_35,B_36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(k6_tmap_1(A_35,B_36)))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_329,plain,(
    ! [C_193,B_192,F_195,D_194,A_196] :
      ( r1_tmap_1(D_194,A_196,k2_tmap_1(B_192,A_196,C_193,D_194),F_195)
      | ~ r1_tmap_1(B_192,A_196,C_193,F_195)
      | ~ m1_subset_1(F_195,u1_struct_0(D_194))
      | ~ m1_subset_1(F_195,u1_struct_0(B_192))
      | ~ m1_pre_topc(D_194,B_192)
      | v2_struct_0(D_194)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_192),u1_struct_0(A_196))))
      | ~ v1_funct_2(C_193,u1_struct_0(B_192),u1_struct_0(A_196))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_192)
      | ~ v2_pre_topc(B_192)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_333,plain,(
    ! [D_197,A_198,B_199,F_200] :
      ( r1_tmap_1(D_197,k6_tmap_1(A_198,B_199),k2_tmap_1(A_198,k6_tmap_1(A_198,B_199),k7_tmap_1(A_198,B_199),D_197),F_200)
      | ~ r1_tmap_1(A_198,k6_tmap_1(A_198,B_199),k7_tmap_1(A_198,B_199),F_200)
      | ~ m1_subset_1(F_200,u1_struct_0(D_197))
      | ~ m1_subset_1(F_200,u1_struct_0(A_198))
      | ~ m1_pre_topc(D_197,A_198)
      | v2_struct_0(D_197)
      | ~ v1_funct_2(k7_tmap_1(A_198,B_199),u1_struct_0(A_198),u1_struct_0(k6_tmap_1(A_198,B_199)))
      | ~ v1_funct_1(k7_tmap_1(A_198,B_199))
      | ~ l1_pre_topc(k6_tmap_1(A_198,B_199))
      | ~ v2_pre_topc(k6_tmap_1(A_198,B_199))
      | v2_struct_0(k6_tmap_1(A_198,B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_32,c_329])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_336,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_333,c_48])).

tff(c_339,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_197,c_174,c_205,c_54,c_50,c_336])).

tff(c_340,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_226,c_56,c_339])).

tff(c_341,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_344,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_341])).

tff(c_347,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_344])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_347])).

tff(c_350,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_352,plain,(
    ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_355,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_352])).

tff(c_358,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_355])).

tff(c_359,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_150,c_358])).

tff(c_362,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_359])).

tff(c_365,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_362])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_365])).

tff(c_368,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_372,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_266,c_368])).

tff(c_375,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_375])).

tff(c_378,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_473,plain,(
    ! [A_221,B_222] :
      ( m1_subset_1(k1_connsp_2(A_221,B_222),k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_subset_1(B_222,u1_struct_0(A_221))
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( v1_xboole_0(B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_513,plain,(
    ! [A_238,B_239] :
      ( v1_xboole_0(k1_connsp_2(A_238,B_239))
      | ~ v1_xboole_0(u1_struct_0(A_238))
      | ~ m1_subset_1(B_239,u1_struct_0(A_238))
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_473,c_12])).

tff(c_519,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_5','#skF_6'))
    | ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_513])).

tff(c_523,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_77,c_378,c_519])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_458,c_523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.53  
% 3.57/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.53  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 3.57/1.53  
% 3.57/1.53  %Foreground sorts:
% 3.57/1.53  
% 3.57/1.53  
% 3.57/1.53  %Background operators:
% 3.57/1.53  
% 3.57/1.53  
% 3.57/1.53  %Foreground operators:
% 3.57/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.57/1.53  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 3.57/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.53  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.57/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.57/1.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.57/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.57/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.57/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.57/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.53  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.57/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.57/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.57/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.57/1.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.57/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.53  
% 3.57/1.55  tff(f_245, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 3.57/1.55  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.57/1.55  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.57/1.55  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.57/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.57/1.55  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.57/1.55  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.57/1.55  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.57/1.55  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 3.57/1.55  tff(f_147, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 3.57/1.55  tff(f_163, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 3.57/1.55  tff(f_132, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.57/1.55  tff(f_221, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.57/1.55  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.57/1.55  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.57/1.55  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_137, plain, (![B_141, A_142]: (v2_pre_topc(B_141) | ~m1_pre_topc(B_141, A_142) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.57/1.55  tff(c_140, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_137])).
% 3.57/1.55  tff(c_143, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_140])).
% 3.57/1.55  tff(c_71, plain, (![B_123, A_124]: (l1_pre_topc(B_123) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.55  tff(c_74, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_71])).
% 3.57/1.55  tff(c_77, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_74])).
% 3.57/1.55  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_446, plain, (![B_213, A_214]: (r2_hidden(B_213, k1_connsp_2(A_214, B_213)) | ~m1_subset_1(B_213, u1_struct_0(A_214)) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.57/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.57/1.55  tff(c_451, plain, (![A_215, B_216]: (~v1_xboole_0(k1_connsp_2(A_215, B_216)) | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_446, c_2])).
% 3.57/1.55  tff(c_454, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_451])).
% 3.57/1.55  tff(c_457, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_77, c_454])).
% 3.57/1.55  tff(c_458, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_457])).
% 3.57/1.55  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_261, plain, (![C_164, A_165, B_166]: (m1_subset_1(C_164, u1_struct_0(A_165)) | ~m1_subset_1(C_164, u1_struct_0(B_166)) | ~m1_pre_topc(B_166, A_165) | v2_struct_0(B_166) | ~l1_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.57/1.55  tff(c_263, plain, (![A_165]: (m1_subset_1('#skF_6', u1_struct_0(A_165)) | ~m1_pre_topc('#skF_5', A_165) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_50, c_261])).
% 3.57/1.55  tff(c_266, plain, (![A_165]: (m1_subset_1('#skF_6', u1_struct_0(A_165)) | ~m1_pre_topc('#skF_5', A_165) | ~l1_pre_topc(A_165) | v2_struct_0(A_165))), inference(negUnitSimplification, [status(thm)], [c_56, c_263])).
% 3.57/1.55  tff(c_14, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/1.55  tff(c_52, plain, (r1_xboole_0(u1_struct_0('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_101, plain, (![A_137, B_138, C_139]: (~r1_xboole_0(A_137, B_138) | ~r2_hidden(C_139, B_138) | ~r2_hidden(C_139, A_137))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.57/1.55  tff(c_111, plain, (![C_140]: (~r2_hidden(C_140, '#skF_4') | ~r2_hidden(C_140, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_52, c_101])).
% 3.57/1.55  tff(c_129, plain, (![A_13]: (~r2_hidden(A_13, '#skF_4') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_13, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_14, c_111])).
% 3.57/1.55  tff(c_146, plain, (![A_143]: (~r2_hidden(A_143, '#skF_4') | ~m1_subset_1(A_143, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_129])).
% 3.57/1.55  tff(c_150, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_146])).
% 3.57/1.55  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_44, plain, (![A_39, B_43, C_45]: (r1_tmap_1(A_39, k6_tmap_1(A_39, B_43), k7_tmap_1(A_39, B_43), C_45) | r2_hidden(C_45, B_43) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_181])).
% 3.57/1.55  tff(c_34, plain, (![A_35, B_36]: (v1_funct_2(k7_tmap_1(A_35, B_36), u1_struct_0(A_35), u1_struct_0(k6_tmap_1(A_35, B_36))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.57/1.55  tff(c_219, plain, (![A_156, B_157]: (~v2_struct_0(k6_tmap_1(A_156, B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.57/1.55  tff(c_222, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_219])).
% 3.57/1.55  tff(c_225, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_222])).
% 3.57/1.55  tff(c_226, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_225])).
% 3.57/1.55  tff(c_190, plain, (![A_148, B_149]: (v2_pre_topc(k6_tmap_1(A_148, B_149)) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148) | ~v2_pre_topc(A_148) | v2_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.57/1.55  tff(c_193, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_190])).
% 3.57/1.55  tff(c_196, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_193])).
% 3.57/1.55  tff(c_197, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_196])).
% 3.57/1.55  tff(c_167, plain, (![A_145, B_146]: (l1_pre_topc(k6_tmap_1(A_145, B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.57/1.55  tff(c_170, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_167])).
% 3.57/1.55  tff(c_173, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_170])).
% 3.57/1.55  tff(c_174, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_173])).
% 3.57/1.55  tff(c_198, plain, (![A_150, B_151]: (v1_funct_1(k7_tmap_1(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.57/1.55  tff(c_201, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_198])).
% 3.57/1.55  tff(c_204, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_201])).
% 3.57/1.55  tff(c_205, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_204])).
% 3.57/1.55  tff(c_32, plain, (![A_35, B_36]: (m1_subset_1(k7_tmap_1(A_35, B_36), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(k6_tmap_1(A_35, B_36))))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.57/1.55  tff(c_329, plain, (![C_193, B_192, F_195, D_194, A_196]: (r1_tmap_1(D_194, A_196, k2_tmap_1(B_192, A_196, C_193, D_194), F_195) | ~r1_tmap_1(B_192, A_196, C_193, F_195) | ~m1_subset_1(F_195, u1_struct_0(D_194)) | ~m1_subset_1(F_195, u1_struct_0(B_192)) | ~m1_pre_topc(D_194, B_192) | v2_struct_0(D_194) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_192), u1_struct_0(A_196)))) | ~v1_funct_2(C_193, u1_struct_0(B_192), u1_struct_0(A_196)) | ~v1_funct_1(C_193) | ~l1_pre_topc(B_192) | ~v2_pre_topc(B_192) | v2_struct_0(B_192) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_221])).
% 3.57/1.55  tff(c_333, plain, (![D_197, A_198, B_199, F_200]: (r1_tmap_1(D_197, k6_tmap_1(A_198, B_199), k2_tmap_1(A_198, k6_tmap_1(A_198, B_199), k7_tmap_1(A_198, B_199), D_197), F_200) | ~r1_tmap_1(A_198, k6_tmap_1(A_198, B_199), k7_tmap_1(A_198, B_199), F_200) | ~m1_subset_1(F_200, u1_struct_0(D_197)) | ~m1_subset_1(F_200, u1_struct_0(A_198)) | ~m1_pre_topc(D_197, A_198) | v2_struct_0(D_197) | ~v1_funct_2(k7_tmap_1(A_198, B_199), u1_struct_0(A_198), u1_struct_0(k6_tmap_1(A_198, B_199))) | ~v1_funct_1(k7_tmap_1(A_198, B_199)) | ~l1_pre_topc(k6_tmap_1(A_198, B_199)) | ~v2_pre_topc(k6_tmap_1(A_198, B_199)) | v2_struct_0(k6_tmap_1(A_198, B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(resolution, [status(thm)], [c_32, c_329])).
% 3.57/1.55  tff(c_48, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_245])).
% 3.57/1.55  tff(c_336, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_333, c_48])).
% 3.57/1.55  tff(c_339, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_197, c_174, c_205, c_54, c_50, c_336])).
% 3.57/1.55  tff(c_340, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_226, c_56, c_339])).
% 3.57/1.55  tff(c_341, plain, (~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_340])).
% 3.57/1.55  tff(c_344, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_341])).
% 3.57/1.55  tff(c_347, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_344])).
% 3.57/1.55  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_347])).
% 3.57/1.55  tff(c_350, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_340])).
% 3.57/1.55  tff(c_352, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_350])).
% 3.57/1.55  tff(c_355, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_352])).
% 3.57/1.55  tff(c_358, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_355])).
% 3.57/1.55  tff(c_359, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_150, c_358])).
% 3.57/1.55  tff(c_362, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_266, c_359])).
% 3.57/1.55  tff(c_365, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_362])).
% 3.57/1.55  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_365])).
% 3.57/1.55  tff(c_368, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_350])).
% 3.57/1.55  tff(c_372, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_266, c_368])).
% 3.57/1.55  tff(c_375, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_372])).
% 3.57/1.55  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_375])).
% 3.57/1.55  tff(c_378, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_129])).
% 3.57/1.55  tff(c_473, plain, (![A_221, B_222]: (m1_subset_1(k1_connsp_2(A_221, B_222), k1_zfmisc_1(u1_struct_0(A_221))) | ~m1_subset_1(B_222, u1_struct_0(A_221)) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.57/1.55  tff(c_12, plain, (![B_12, A_10]: (v1_xboole_0(B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.57/1.55  tff(c_513, plain, (![A_238, B_239]: (v1_xboole_0(k1_connsp_2(A_238, B_239)) | ~v1_xboole_0(u1_struct_0(A_238)) | ~m1_subset_1(B_239, u1_struct_0(A_238)) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238))), inference(resolution, [status(thm)], [c_473, c_12])).
% 3.57/1.55  tff(c_519, plain, (v1_xboole_0(k1_connsp_2('#skF_5', '#skF_6')) | ~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_513])).
% 3.57/1.55  tff(c_523, plain, (v1_xboole_0(k1_connsp_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_77, c_378, c_519])).
% 3.57/1.55  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_458, c_523])).
% 3.57/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/1.55  
% 3.57/1.55  Inference rules
% 3.57/1.55  ----------------------
% 3.57/1.55  #Ref     : 0
% 3.57/1.55  #Sup     : 75
% 3.57/1.55  #Fact    : 0
% 3.57/1.55  #Define  : 0
% 3.57/1.55  #Split   : 12
% 3.57/1.55  #Chain   : 0
% 3.57/1.55  #Close   : 0
% 3.57/1.55  
% 3.57/1.55  Ordering : KBO
% 3.57/1.55  
% 3.57/1.55  Simplification rules
% 3.57/1.55  ----------------------
% 3.57/1.55  #Subsume      : 9
% 3.57/1.55  #Demod        : 61
% 3.57/1.55  #Tautology    : 6
% 3.57/1.55  #SimpNegUnit  : 25
% 3.57/1.55  #BackRed      : 0
% 3.57/1.55  
% 3.57/1.55  #Partial instantiations: 0
% 3.57/1.55  #Strategies tried      : 1
% 3.57/1.55  
% 3.57/1.55  Timing (in seconds)
% 3.57/1.55  ----------------------
% 3.57/1.56  Preprocessing        : 0.36
% 3.57/1.56  Parsing              : 0.21
% 3.57/1.56  CNF conversion       : 0.03
% 3.57/1.56  Main loop            : 0.34
% 3.57/1.56  Inferencing          : 0.14
% 3.57/1.56  Reduction            : 0.10
% 3.57/1.56  Demodulation         : 0.06
% 3.57/1.56  BG Simplification    : 0.02
% 3.57/1.56  Subsumption          : 0.07
% 3.57/1.56  Abstraction          : 0.01
% 3.57/1.56  MUC search           : 0.00
% 3.57/1.56  Cooper               : 0.00
% 3.57/1.56  Total                : 0.75
% 3.57/1.56  Index Insertion      : 0.00
% 3.57/1.56  Index Deletion       : 0.00
% 3.57/1.56  Index Matching       : 0.00
% 3.57/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
