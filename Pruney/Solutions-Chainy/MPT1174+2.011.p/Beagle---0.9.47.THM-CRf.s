%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 725 expanded)
%              Number of leaves         :   37 ( 304 expanded)
%              Depth                    :   31
%              Number of atoms          :  387 (3958 expanded)
%              Number of equality atoms :   41 ( 543 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_orders_1(C,k1_orders_1(u1_struct_0(A)))
               => ! [D] :
                    ( m2_orders_2(D,A,C)
                   => ( B = k1_funct_1(C,u1_struct_0(A))
                     => k3_orders_2(A,D,B) = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_mcart_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_170,axiom,(
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
                  ( m1_orders_1(D,k1_orders_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m2_orders_2(E,A,D)
                     => ( ( r2_hidden(B,E)
                          & C = k1_funct_1(D,u1_struct_0(A)) )
                       => r3_orders_2(A,C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

tff(c_28,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_40,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_34,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_32,plain,(
    m2_orders_2('#skF_5','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_92,plain,(
    ! [C_119,A_120,B_121] :
      ( m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m2_orders_2(C_119,A_120,B_121)
      | ~ m1_orders_1(B_121,k1_orders_1(u1_struct_0(A_120)))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120)
      | ~ v4_orders_2(A_120)
      | ~ v3_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_94,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_97,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_34,c_94])).

tff(c_98,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_97])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_6,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_1'(A_4),A_4)
      | k1_xboole_0 = A_4 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k3_orders_2(A_122,B_123,C_124),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_orders_2(A_122)
      | ~ v5_orders_2(A_122)
      | ~ v4_orders_2(A_122)
      | ~ v3_orders_2(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_132,A_133,B_134,C_135] :
      ( m1_subset_1(A_132,u1_struct_0(A_133))
      | ~ r2_hidden(A_132,k3_orders_2(A_133,B_134,C_135))
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_149,plain,(
    ! [A_133,B_134,C_135] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_133,B_134,C_135)),u1_struct_0(A_133))
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133)
      | k3_orders_2(A_133,B_134,C_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_150,plain,(
    ! [B_136,D_137,A_138,C_139] :
      ( r2_hidden(B_136,D_137)
      | ~ r2_hidden(B_136,k3_orders_2(A_138,D_137,C_139))
      | ~ m1_subset_1(D_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ m1_subset_1(C_139,u1_struct_0(A_138))
      | ~ m1_subset_1(B_136,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138)
      | ~ v5_orders_2(A_138)
      | ~ v4_orders_2(A_138)
      | ~ v3_orders_2(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_222,plain,(
    ! [A_158,D_159,C_160] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_158,D_159,C_160)),D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_158,D_159,C_160)),u1_struct_0(A_158))
      | ~ l1_orders_2(A_158)
      | ~ v5_orders_2(A_158)
      | ~ v4_orders_2(A_158)
      | ~ v3_orders_2(A_158)
      | v2_struct_0(A_158)
      | k3_orders_2(A_158,D_159,C_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_150])).

tff(c_234,plain,(
    ! [A_163,B_164,C_165] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_163,B_164,C_165)),B_164)
      | ~ m1_subset_1(C_165,u1_struct_0(A_163))
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163)
      | ~ v4_orders_2(A_163)
      | ~ v3_orders_2(A_163)
      | v2_struct_0(A_163)
      | k3_orders_2(A_163,B_164,C_165) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_149,c_222])).

tff(c_105,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ r2_hidden(A_1,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_227,plain,(
    ! [D_159,C_160] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_159,C_160) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105,c_222])).

tff(c_231,plain,(
    ! [D_159,C_160] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_159,C_160) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_227])).

tff(c_232,plain,(
    ! [D_159,C_160] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_160,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_159,C_160) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_159,C_160)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_231])).

tff(c_237,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_165)),'#skF_5')
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_165) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_234,c_232])).

tff(c_259,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_165)),'#skF_5')
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_165) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_98,c_237])).

tff(c_260,plain,(
    ! [C_165] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_165)),'#skF_5')
      | ~ m1_subset_1(C_165,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_165) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_259])).

tff(c_30,plain,(
    k1_funct_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_273,plain,(
    ! [A_167,D_168,B_169,E_170] :
      ( r3_orders_2(A_167,k1_funct_1(D_168,u1_struct_0(A_167)),B_169)
      | ~ r2_hidden(B_169,E_170)
      | ~ m2_orders_2(E_170,A_167,D_168)
      | ~ m1_orders_1(D_168,k1_orders_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(k1_funct_1(D_168,u1_struct_0(A_167)),u1_struct_0(A_167))
      | ~ m1_subset_1(B_169,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v5_orders_2(A_167)
      | ~ v4_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_308,plain,(
    ! [A_181,D_182,C_183] :
      ( r3_orders_2(A_181,k1_funct_1(D_182,u1_struct_0(A_181)),'#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)))
      | ~ m2_orders_2('#skF_5',A_181,D_182)
      | ~ m1_orders_1(D_182,k1_orders_1(u1_struct_0(A_181)))
      | ~ m1_subset_1(k1_funct_1(D_182,u1_struct_0(A_181)),u1_struct_0(A_181))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)),u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v5_orders_2(A_181)
      | ~ v4_orders_2(A_181)
      | ~ v3_orders_2(A_181)
      | v2_struct_0(A_181)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_183) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_260,c_273])).

tff(c_313,plain,(
    ! [C_183] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)))
      | ~ m2_orders_2('#skF_5','#skF_2','#skF_4')
      | ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k1_funct_1('#skF_4',u1_struct_0('#skF_2')),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_183) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_308])).

tff(c_316,plain,(
    ! [C_183] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_183)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_183) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_36,c_30,c_34,c_32,c_313])).

tff(c_318,plain,(
    ! [C_184] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_184)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_184)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_184) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_316])).

tff(c_322,plain,(
    ! [C_135] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_135)))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_149,c_318])).

tff(c_328,plain,(
    ! [C_135] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_135)))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_135) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_98,c_322])).

tff(c_331,plain,(
    ! [C_185] :
      ( r3_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_185)))
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_185) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_328])).

tff(c_16,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_orders_2(A_25,B_26,C_27)
      | ~ r3_orders_2(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,u1_struct_0(A_25))
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_333,plain,(
    ! [C_185] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_185)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_185)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_185) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_331,c_16])).

tff(c_336,plain,(
    ! [C_185] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_185)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_185)),u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_185) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_36,c_333])).

tff(c_338,plain,(
    ! [C_186] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_186)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5',C_186)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_186,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_186) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_336])).

tff(c_342,plain,(
    ! [C_135] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_135)))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_135) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_149,c_338])).

tff(c_348,plain,(
    ! [C_135] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_135)))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2','#skF_5',C_135) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_98,c_342])).

tff(c_351,plain,(
    ! [C_187] :
      ( r1_orders_2('#skF_2','#skF_3','#skF_1'(k3_orders_2('#skF_2','#skF_5',C_187)))
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2','#skF_5',C_187) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_348])).

tff(c_174,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( r2_orders_2(A_143,B_144,C_145)
      | ~ r2_hidden(B_144,k3_orders_2(A_143,D_146,C_145))
      | ~ m1_subset_1(D_146,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143)
      | ~ v5_orders_2(A_143)
      | ~ v4_orders_2(A_143)
      | ~ v3_orders_2(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_286,plain,(
    ! [A_171,D_172,C_173] :
      ( r2_orders_2(A_171,'#skF_1'(k3_orders_2(A_171,D_172,C_173)),C_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ m1_subset_1(C_173,u1_struct_0(A_171))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_171,D_172,C_173)),u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | ~ v5_orders_2(A_171)
      | ~ v4_orders_2(A_171)
      | ~ v3_orders_2(A_171)
      | v2_struct_0(A_171)
      | k3_orders_2(A_171,D_172,C_173) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_174])).

tff(c_291,plain,(
    ! [D_172,C_173] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_172,C_173)),C_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_173,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_172,C_173) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_172,C_173)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105,c_286])).

tff(c_295,plain,(
    ! [D_172,C_173] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_172,C_173)),C_173)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_173,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | k3_orders_2('#skF_2',D_172,C_173) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_172,C_173)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_291])).

tff(c_297,plain,(
    ! [D_174,C_175] :
      ( r2_orders_2('#skF_2','#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),C_175)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_174,C_175) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_295])).

tff(c_18,plain,(
    ! [A_28,C_34,B_32] :
      ( ~ r2_orders_2(A_28,C_34,B_32)
      | ~ r1_orders_2(A_28,B_32,C_34)
      | ~ m1_subset_1(C_34,u1_struct_0(A_28))
      | ~ m1_subset_1(B_32,u1_struct_0(A_28))
      | ~ l1_orders_2(A_28)
      | ~ v5_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_299,plain,(
    ! [C_175,D_174] :
      ( ~ r1_orders_2('#skF_2',C_175,'#skF_1'(k3_orders_2('#skF_2',D_174,C_175)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_174,C_175) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_297,c_18])).

tff(c_302,plain,(
    ! [C_175,D_174] :
      ( ~ r1_orders_2('#skF_2',C_175,'#skF_1'(k3_orders_2('#skF_2',D_174,C_175)))
      | ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_175,u1_struct_0('#skF_2'))
      | k3_orders_2('#skF_2',D_174,C_175) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2',D_174,C_175)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_299])).

tff(c_354,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_351,c_302])).

tff(c_357,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_98,c_354])).

tff(c_358,plain,
    ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_357])).

tff(c_369,plain,(
    ~ r2_hidden('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_372,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_260,c_369])).

tff(c_378,plain,(
    k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_372])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_378])).

tff(c_381,plain,(
    ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_2','#skF_5','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_407,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_381])).

tff(c_413,plain,
    ( v2_struct_0('#skF_2')
    | k3_orders_2('#skF_2','#skF_5','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_98,c_36,c_407])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_46,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  
% 3.16/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.54  %$ r3_orders_2 > r2_orders_2 > r1_orders_2 > m2_orders_2 > v6_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.16/1.54  
% 3.16/1.54  %Foreground sorts:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Background operators:
% 3.16/1.54  
% 3.16/1.54  
% 3.16/1.54  %Foreground operators:
% 3.16/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.16/1.54  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.16/1.54  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.54  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.16/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.54  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.16/1.54  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 3.16/1.54  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 3.16/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.16/1.54  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.16/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.54  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.16/1.54  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.54  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.16/1.54  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 3.16/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.16/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.54  
% 3.16/1.57  tff(f_195, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_orders_1(C, k1_orders_1(u1_struct_0(A))) => (![D]: (m2_orders_2(D, A, C) => ((B = k1_funct_1(C, u1_struct_0(A))) => (k3_orders_2(A, D, B) = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_orders_2)).
% 3.16/1.57  tff(f_85, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 3.16/1.57  tff(f_48, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: (((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_mcart_1)).
% 3.16/1.57  tff(f_65, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 3.16/1.57  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.16/1.57  tff(f_141, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.16/1.57  tff(f_170, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_orders_1(D, k1_orders_1(u1_struct_0(A))) => (![E]: (m2_orders_2(E, A, D) => ((r2_hidden(B, E) & (C = k1_funct_1(D, u1_struct_0(A)))) => r3_orders_2(A, C, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_orders_2)).
% 3.16/1.57  tff(f_100, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.16/1.57  tff(f_115, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_orders_2)).
% 3.16/1.57  tff(c_28, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_44, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_42, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_40, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_34, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_32, plain, (m2_orders_2('#skF_5', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_92, plain, (![C_119, A_120, B_121]: (m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_120))) | ~m2_orders_2(C_119, A_120, B_121) | ~m1_orders_1(B_121, k1_orders_1(u1_struct_0(A_120))) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120) | ~v4_orders_2(A_120) | ~v3_orders_2(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.16/1.57  tff(c_94, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_92])).
% 3.16/1.57  tff(c_97, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_34, c_94])).
% 3.16/1.57  tff(c_98, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_46, c_97])).
% 3.16/1.57  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_6, plain, (![A_4]: (r2_hidden('#skF_1'(A_4), A_4) | k1_xboole_0=A_4)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.57  tff(c_99, plain, (![A_122, B_123, C_124]: (m1_subset_1(k3_orders_2(A_122, B_123, C_124), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_orders_2(A_122) | ~v5_orders_2(A_122) | ~v4_orders_2(A_122) | ~v3_orders_2(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.57  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.57  tff(c_145, plain, (![A_132, A_133, B_134, C_135]: (m1_subset_1(A_132, u1_struct_0(A_133)) | ~r2_hidden(A_132, k3_orders_2(A_133, B_134, C_135)) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_99, c_2])).
% 3.16/1.57  tff(c_149, plain, (![A_133, B_134, C_135]: (m1_subset_1('#skF_1'(k3_orders_2(A_133, B_134, C_135)), u1_struct_0(A_133)) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133) | k3_orders_2(A_133, B_134, C_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_145])).
% 3.16/1.57  tff(c_150, plain, (![B_136, D_137, A_138, C_139]: (r2_hidden(B_136, D_137) | ~r2_hidden(B_136, k3_orders_2(A_138, D_137, C_139)) | ~m1_subset_1(D_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~m1_subset_1(C_139, u1_struct_0(A_138)) | ~m1_subset_1(B_136, u1_struct_0(A_138)) | ~l1_orders_2(A_138) | ~v5_orders_2(A_138) | ~v4_orders_2(A_138) | ~v3_orders_2(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.57  tff(c_222, plain, (![A_158, D_159, C_160]: (r2_hidden('#skF_1'(k3_orders_2(A_158, D_159, C_160)), D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0(A_158))) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_158, D_159, C_160)), u1_struct_0(A_158)) | ~l1_orders_2(A_158) | ~v5_orders_2(A_158) | ~v4_orders_2(A_158) | ~v3_orders_2(A_158) | v2_struct_0(A_158) | k3_orders_2(A_158, D_159, C_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_150])).
% 3.16/1.57  tff(c_234, plain, (![A_163, B_164, C_165]: (r2_hidden('#skF_1'(k3_orders_2(A_163, B_164, C_165)), B_164) | ~m1_subset_1(C_165, u1_struct_0(A_163)) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163) | ~v4_orders_2(A_163) | ~v3_orders_2(A_163) | v2_struct_0(A_163) | k3_orders_2(A_163, B_164, C_165)=k1_xboole_0)), inference(resolution, [status(thm)], [c_149, c_222])).
% 3.16/1.57  tff(c_105, plain, (![A_1]: (m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~r2_hidden(A_1, '#skF_5'))), inference(resolution, [status(thm)], [c_98, c_2])).
% 3.16/1.57  tff(c_227, plain, (![D_159, C_160]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_160, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_159, C_160)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), '#skF_5'))), inference(resolution, [status(thm)], [c_105, c_222])).
% 3.16/1.57  tff(c_231, plain, (![D_159, C_160]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_160, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_159, C_160)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_227])).
% 3.16/1.57  tff(c_232, plain, (![D_159, C_160]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_160, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_159, C_160)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_159, C_160)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_231])).
% 3.16/1.57  tff(c_237, plain, (![C_165]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_165)), '#skF_5') | ~m1_subset_1(C_165, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_165)=k1_xboole_0)), inference(resolution, [status(thm)], [c_234, c_232])).
% 3.16/1.57  tff(c_259, plain, (![C_165]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_165)), '#skF_5') | ~m1_subset_1(C_165, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_165)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_98, c_237])).
% 3.16/1.57  tff(c_260, plain, (![C_165]: (r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_165)), '#skF_5') | ~m1_subset_1(C_165, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_165)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_259])).
% 3.16/1.57  tff(c_30, plain, (k1_funct_1('#skF_4', u1_struct_0('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.16/1.57  tff(c_273, plain, (![A_167, D_168, B_169, E_170]: (r3_orders_2(A_167, k1_funct_1(D_168, u1_struct_0(A_167)), B_169) | ~r2_hidden(B_169, E_170) | ~m2_orders_2(E_170, A_167, D_168) | ~m1_orders_1(D_168, k1_orders_1(u1_struct_0(A_167))) | ~m1_subset_1(k1_funct_1(D_168, u1_struct_0(A_167)), u1_struct_0(A_167)) | ~m1_subset_1(B_169, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v5_orders_2(A_167) | ~v4_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.16/1.57  tff(c_308, plain, (![A_181, D_182, C_183]: (r3_orders_2(A_181, k1_funct_1(D_182, u1_struct_0(A_181)), '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183))) | ~m2_orders_2('#skF_5', A_181, D_182) | ~m1_orders_1(D_182, k1_orders_1(u1_struct_0(A_181))) | ~m1_subset_1(k1_funct_1(D_182, u1_struct_0(A_181)), u1_struct_0(A_181)) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183)), u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v5_orders_2(A_181) | ~v4_orders_2(A_181) | ~v3_orders_2(A_181) | v2_struct_0(A_181) | ~m1_subset_1(C_183, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_183)=k1_xboole_0)), inference(resolution, [status(thm)], [c_260, c_273])).
% 3.16/1.57  tff(c_313, plain, (![C_183]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183))) | ~m2_orders_2('#skF_5', '#skF_2', '#skF_4') | ~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k1_funct_1('#skF_4', u1_struct_0('#skF_2')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_183, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_183)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_308])).
% 3.16/1.57  tff(c_316, plain, (![C_183]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_183)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_183, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_36, c_30, c_34, c_32, c_313])).
% 3.16/1.57  tff(c_318, plain, (![C_184]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_184))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_184)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_184, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_184)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_316])).
% 3.16/1.57  tff(c_322, plain, (![C_135]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_135))) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_149, c_318])).
% 3.16/1.57  tff(c_328, plain, (![C_135]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_135))) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_98, c_322])).
% 3.16/1.57  tff(c_331, plain, (![C_185]: (r3_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_185))) | ~m1_subset_1(C_185, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_185)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_328])).
% 3.16/1.57  tff(c_16, plain, (![A_25, B_26, C_27]: (r1_orders_2(A_25, B_26, C_27) | ~r3_orders_2(A_25, B_26, C_27) | ~m1_subset_1(C_27, u1_struct_0(A_25)) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_orders_2(A_25) | ~v3_orders_2(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.16/1.57  tff(c_333, plain, (![C_185]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_185))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_185)), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(C_185, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_185)=k1_xboole_0)), inference(resolution, [status(thm)], [c_331, c_16])).
% 3.16/1.57  tff(c_336, plain, (![C_185]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_185))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_185)), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_185, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_185)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_36, c_333])).
% 3.16/1.57  tff(c_338, plain, (![C_186]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_186))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_186)), u1_struct_0('#skF_2')) | ~m1_subset_1(C_186, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_186)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_336])).
% 3.16/1.57  tff(c_342, plain, (![C_135]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_135))) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_149, c_338])).
% 3.16/1.57  tff(c_348, plain, (![C_135]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_135))) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', C_135)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_98, c_342])).
% 3.16/1.57  tff(c_351, plain, (![C_187]: (r1_orders_2('#skF_2', '#skF_3', '#skF_1'(k3_orders_2('#skF_2', '#skF_5', C_187))) | ~m1_subset_1(C_187, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', C_187)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_46, c_348])).
% 3.16/1.57  tff(c_174, plain, (![A_143, B_144, C_145, D_146]: (r2_orders_2(A_143, B_144, C_145) | ~r2_hidden(B_144, k3_orders_2(A_143, D_146, C_145)) | ~m1_subset_1(D_146, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143) | ~v5_orders_2(A_143) | ~v4_orders_2(A_143) | ~v3_orders_2(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.16/1.57  tff(c_286, plain, (![A_171, D_172, C_173]: (r2_orders_2(A_171, '#skF_1'(k3_orders_2(A_171, D_172, C_173)), C_173) | ~m1_subset_1(D_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~m1_subset_1(C_173, u1_struct_0(A_171)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_171, D_172, C_173)), u1_struct_0(A_171)) | ~l1_orders_2(A_171) | ~v5_orders_2(A_171) | ~v4_orders_2(A_171) | ~v3_orders_2(A_171) | v2_struct_0(A_171) | k3_orders_2(A_171, D_172, C_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_174])).
% 3.16/1.57  tff(c_291, plain, (![D_172, C_173]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_172, C_173)), C_173) | ~m1_subset_1(D_172, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_173, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_172, C_173)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_172, C_173)), '#skF_5'))), inference(resolution, [status(thm)], [c_105, c_286])).
% 3.16/1.57  tff(c_295, plain, (![D_172, C_173]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_172, C_173)), C_173) | ~m1_subset_1(D_172, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_173, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', D_172, C_173)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_172, C_173)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_291])).
% 3.16/1.57  tff(c_297, plain, (![D_174, C_175]: (r2_orders_2('#skF_2', '#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), C_175) | ~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_175, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_174, C_175)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_295])).
% 3.16/1.57  tff(c_18, plain, (![A_28, C_34, B_32]: (~r2_orders_2(A_28, C_34, B_32) | ~r1_orders_2(A_28, B_32, C_34) | ~m1_subset_1(C_34, u1_struct_0(A_28)) | ~m1_subset_1(B_32, u1_struct_0(A_28)) | ~l1_orders_2(A_28) | ~v5_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.16/1.57  tff(c_299, plain, (![C_175, D_174]: (~r1_orders_2('#skF_2', C_175, '#skF_1'(k3_orders_2('#skF_2', D_174, C_175))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_175, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_174, C_175)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), '#skF_5'))), inference(resolution, [status(thm)], [c_297, c_18])).
% 3.16/1.57  tff(c_302, plain, (![C_175, D_174]: (~r1_orders_2('#skF_2', C_175, '#skF_1'(k3_orders_2('#skF_2', D_174, C_175))) | ~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), u1_struct_0('#skF_2')) | ~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_175, u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', D_174, C_175)=k1_xboole_0 | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', D_174, C_175)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_299])).
% 3.16/1.57  tff(c_354, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_351, c_302])).
% 3.16/1.57  tff(c_357, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_98, c_354])).
% 3.16/1.57  tff(c_358, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_28, c_357])).
% 3.16/1.57  tff(c_369, plain, (~r2_hidden('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), '#skF_5')), inference(splitLeft, [status(thm)], [c_358])).
% 3.16/1.57  tff(c_372, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_260, c_369])).
% 3.16/1.57  tff(c_378, plain, (k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_372])).
% 3.16/1.57  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_378])).
% 3.16/1.57  tff(c_381, plain, (~m1_subset_1('#skF_1'(k3_orders_2('#skF_2', '#skF_5', '#skF_3')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_358])).
% 3.16/1.57  tff(c_407, plain, (~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_381])).
% 3.16/1.57  tff(c_413, plain, (v2_struct_0('#skF_2') | k3_orders_2('#skF_2', '#skF_5', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_98, c_36, c_407])).
% 3.16/1.57  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_46, c_413])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 67
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 2
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 7
% 3.16/1.57  #Demod        : 114
% 3.16/1.57  #Tautology    : 10
% 3.16/1.57  #SimpNegUnit  : 28
% 3.16/1.57  #BackRed      : 0
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 0
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.34
% 3.16/1.58  Parsing              : 0.19
% 3.16/1.58  CNF conversion       : 0.03
% 3.16/1.58  Main loop            : 0.42
% 3.16/1.58  Inferencing          : 0.19
% 3.16/1.58  Reduction            : 0.11
% 3.16/1.58  Demodulation         : 0.07
% 3.16/1.58  BG Simplification    : 0.02
% 3.16/1.58  Subsumption          : 0.07
% 3.16/1.58  Abstraction          : 0.02
% 3.16/1.58  MUC search           : 0.00
% 3.16/1.58  Cooper               : 0.00
% 3.16/1.58  Total                : 0.81
% 3.16/1.58  Index Insertion      : 0.00
% 3.16/1.58  Index Deletion       : 0.00
% 3.16/1.58  Index Matching       : 0.00
% 3.16/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
